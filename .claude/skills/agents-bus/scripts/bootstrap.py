"""Discovery and conservative, retryable creation of one coordination domain.

Only a matching join id resolves competing valid buses. An explicit path and
an environment hint both participate in discovery, and no override hides a
corrupt candidate. Initialization deliberately chooses its explicit root.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import uuid

from common import BusError, identifier, load_bus, read_json, utc, write_bytes, write_json
from common import validate_bindings as _bindings


DIRECTORIES = (".messages", ".staging", "checkpoints", "heartbeat", "inbox",
               "locks", "participants")
SCHEMA = 2


def _root(path: Path) -> Path:
    try:
        result = Path(path).resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise BusError(f"Invalid coordination root: {path}") from error
    if not result.is_dir():
        raise BusError(f"Coordination root must be an existing directory: {result}")
    return result


def _identity(path: Path) -> tuple[Path, dict]:
    try:
        resolved = path.resolve(strict=True)
        identity = load_bus(resolved)
    except (OSError, RuntimeError, TypeError) as error:
        raise BusError(f"Unreadable or invalid bus candidate: {path}") from error
    if (resolved / "bus.json").is_symlink():
        raise BusError(f"Bus identity must be a regular file: {path}")
    if not isinstance(identity.get("created_at"), str) or not identity["created_at"]:
        raise BusError(f"Missing bus creation timestamp: {path}")
    if not isinstance(identity.get("package"), dict):
        raise BusError(f"Invalid creating-package identity: {path}")
    _package(identity["package"])
    return resolved, identity


def _marker(path: Path) -> tuple[Path, dict]:
    record = read_json(path)
    target = record.get("bus_path")
    if (record.get("schema_version") != SCHEMA or not isinstance(target, str)
            or not Path(target).is_absolute()
            or not re.fullmatch(r"[0-9a-f]{16}", str(record.get("bus_id", "")))):
        raise BusError(f"Invalid bus marker: {path}")
    actual, identity = _identity(Path(target))
    if record["bus_id"] != identity["bus_id"]:
        raise BusError(f"Marker and bus identity disagree: {path}")
    return actual, identity


def discover(root: Path | None = None, *, explicit: Path | None = None,
             environment: Path | None = None, join: str | None = None) -> Path:
    """Validate all candidates, then select one bus, with --join for conflicts.

    ``root`` fixes marker discovery independently of the process working
    directory. Relative explicit/environment paths follow ordinary cwd rules.
    Omit ``environment`` to read AGENTS_BUS, when set.
    """
    start = _root(root if root is not None else Path.cwd())
    if join is not None and not re.fullmatch(r"[0-9a-f]{16}", join):
        raise BusError("Join must name a 16-hex bus id")
    candidates: dict[tuple[Path, str], dict] = {}
    hints = []
    if explicit is not None:
        hints.append(Path(explicit))
    env = environment if environment is not None else os.environ.get("AGENTS_BUS")
    if isinstance(env, str) and not env.strip():
        env = None
    if env is not None:
        hints.append(Path(env))
    for hint in hints:
        actual, identity = _identity(hint)
        key = (actual, identity["bus_id"])
        candidates[key] = identity
    for ancestor in (start, *start.parents):
        marker = ancestor / ".agents_bus"
        if os.path.lexists(marker):
            actual, identity = _marker(marker)
            candidates[(actual, identity["bus_id"])] = identity
    if not candidates:
        raise BusError("No bus here; initialize an explicitly chosen root or name its bus")
    if join is not None:
        matches = [key for key in candidates if key[1] == join]
        if len(matches) != 1:
            raise BusError(f"Join id does not uniquely identify a candidate: {join}")
        return matches[0][0]
    if len(candidates) == 1:
        return next(iter(candidates))[0]
    choices = "; ".join(f"{identity} at {path}" for path, identity in candidates)
    raise BusError(f"Ambiguous buses; explicitly select --join: {choices}")


def _directory(path: Path) -> None:
    """Never adopt a control-directory symlink or overwrite an existing file."""
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError as error:
        raise BusError(f"Cannot create control directory: {path}") from error
    if path.is_symlink() or not path.is_dir():
        raise BusError(f"Control directory must be a real directory: {path}")


def _text(path: Path) -> None:
    if path.is_symlink() or not path.is_file():
        raise BusError(f"Expected a regular text file: {path}")
    try:
        path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise BusError(f"Unreadable text file: {path}") from error


def _package(package: dict | None) -> dict:
    if package is None:
        manifest = Path(__file__).resolve().parent.parent / "MANIFEST.json"
        package = {"name": "agents-bus", "manifest_sha256":
                   hashlib.sha256(manifest.read_bytes()).hexdigest() if manifest.is_file() else None}
    if not isinstance(package, dict) or not isinstance(package.get("name"), str):
        raise BusError("Package identity must include its name")
    identifier(package["name"])
    digest = package.get("manifest_sha256")
    if digest is not None and (not isinstance(digest, str)
                               or not re.fullmatch(r"[0-9a-f]{64}", digest)):
        raise BusError("Package manifest digest must be SHA256 or null for an unmanifested prototype")
    return dict(package)


def _unidentified_data(bus: Path) -> Path | None:
    """Find live records without treating empty setup directories as history."""
    for name in ("STATE.md", "PROTOCOL.md", "bindings.json"):
        if os.path.lexists(bus / name):
            return bus / name
    for name in DIRECTORIES:
        if name == ".staging":
            continue  # Reserved staging remnants are safe to leave untouched.
        path = bus / name
        if not os.path.lexists(path):
            continue
        if path.is_symlink() or not path.is_dir():
            return path
        try:
            if next(path.iterdir(), None) is not None:
                return path
        except OSError as error:
            raise BusError(f"Cannot inspect unidentified control directory: {path}") from error
    return None


def initialize(root: Path, aliases: list[str], *, bus_path: Path | None = None,
               package: dict | None = None) -> dict:
    """Complete a compatible partial initialization without resetting history.

    Immutable publication adopts a concurrent winner's identity. Every alias's
    directories are added independently; an existing board is never rewritten
    to add aliases (``hello`` later adds its own section under the state guard).
    The discovery marker is published only after the operational files exist.
    """
    root = _root(root)
    if not isinstance(aliases, list):
        raise BusError("Aliases must be a list of identifiers")
    for alias in aliases:
        identifier(alias)
    package = _package(package)
    bus = Path(bus_path if bus_path is not None else root / "tmp" / "agents_bus").resolve()
    marker = root / ".agents_bus"
    if os.path.lexists(marker):
        prior_bus, _ = _marker(marker)
        if prior_bus != bus:
            raise BusError(f"Root already names a different bus: {marker}")
    # Validate existing identity before creating missing directories/templates.
    if os.path.lexists(bus / "bus.json"):
        _, prior = _identity(bus)
        if prior["coordination_root"] != str(root):
            raise BusError("Existing bus belongs to a different coordination root")
    else:
        unidentified = _unidentified_data(bus)
        if unidentified is not None:
            # A compatible concurrent init may have published its identity
            # since our first check; read that winner before refusing.
            if os.path.lexists(bus / "bus.json"):
                _, prior = _identity(bus)
                if prior["coordination_root"] != str(root):
                    raise BusError("Existing bus belongs to a different coordination root")
            else:
                raise BusError(f"Unidentified existing bus data at {unidentified}; "
                               "explicit migration is required")
    _directory(bus)
    record = {"schema_version": SCHEMA, "bus_id": uuid.uuid4().hex[:16],
              "coordination_root": str(root), "created_at": utc(), "package": package}
    write_json(bus / "bus.json", record)
    _, record = _identity(bus)
    if record["coordination_root"] != str(root):
        raise BusError("Concurrent initialization selected an incompatible root")
    # Refuse corrupt existing operational files before adding repair artifacts.
    for name in ("STATE.md", "PROTOCOL.md"):
        if os.path.lexists(bus / name):
            _text(bus / name)
    if os.path.lexists(bus / "bindings.json"):
        _bindings(bus, allow_missing_state=True)
    for name in DIRECTORIES:
        _directory(bus / name)
    for alias in dict.fromkeys(aliases):
        _directory(bus / "inbox" / alias)
        _directory(bus / "inbox" / alias / "done")
    sections = "".join(f"\n## {alias}\n\nNot yet registered.\n" for alias in dict.fromkeys(aliases))
    write_bytes(bus / "STATE.md", ("# Coordination state\n" + sections
                                   + "\n## Shared\n\nNo accepted work recorded.\n").encode())
    _text(bus / "STATE.md")
    write_json(bus / "bindings.json", {"keys": {
        "state": {"resource": str(bus / "STATE.md"), "kind": "board"}}})
    _bindings(bus)
    protocol = ("# Project coordination protocol\n\n"
                f"Use the installed `{record['package']['name']}` skill's `SKILL.md`; "
                "locate it through the current harness's skill catalog. This bus contains "
                "project state, not a copy of the installed package.\n\n"
                "This bus governs one coordination domain. Every shared resource must be "
                "governed by exactly one bus; cross-bus exclusion is not provided.\n\n"
                "Bindings live in `bindings.json`. Participant identity and activation live "
                "in `participants/`. On re-entry read the installed skill's recovery "
                "instructions, this protocol, the state board, current inbox, checkpoints, "
                "heartbeats, and actual locks before writing or resuming work.\n")
    write_bytes(bus / "PROTOCOL.md", protocol.encode())
    _text(bus / "PROTOCOL.md")
    expected = {"schema_version": SCHEMA, "bus_path": str(bus), "bus_id": record["bus_id"]}
    write_json(marker, expected)
    published_path, published_record = _marker(marker)
    if published_path != bus or published_record["bus_id"] != record["bus_id"]:
        raise BusError("Concurrent initialization published a conflicting root marker")
    try:
        ignore_line = "/" + bus.relative_to(root).as_posix() + "/"
    except ValueError:
        ignore_line = None  # An external bus has no repository-relative ignore line.
    return {**record, "path": str(bus), "ignore_line": ignore_line}
