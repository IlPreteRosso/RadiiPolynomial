"""Small filesystem primitives for the isolated universal-bus prototype."""
from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
import uuid

IDENTIFIER = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}\Z")
RESERVED_KEYS = {"meta", "participants"}


class BusError(ValueError):
    """A conflict or invalid request; no implicit recovery is authorized."""


def identifier(value: str) -> str:
    if not isinstance(value, str) or not IDENTIFIER.fullmatch(value):
        raise BusError(f"Invalid identifier: {value!r}")
    return value


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def token_digest(token: str) -> str:
    return hashlib.sha256(token.encode()).hexdigest()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def read_json(path: Path) -> dict:
    try:
        result = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise BusError(f"Unreadable or corrupt record {path}: {error}") from error
    if not isinstance(result, dict):
        raise BusError(f"Expected an object in {path}")
    return result


def write_bytes(path: Path, data: bytes, *, replace: bool = False,
                mode: int = 0o600) -> bool:
    """Publish complete bytes. False means no-replace lost; never overwrite then.

    Callers validate an existing winner. Replacing mutable metadata requires its
    guard. The temporary lives alongside the target, including outside-bus
    markers and token bundles, so publication never crosses filesystems.
    This covers concurrent readers and process interruption, not a guarantee
    against machine power loss (parent directories are not fsynced).
    """
    descriptor, name = tempfile.mkstemp(prefix=".tmp-", dir=path.parent)
    staged = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            os.fchmod(stream.fileno(), mode)
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        if replace:
            os.replace(staged, path)
        else:
            try:
                os.link(staged, path)
            except FileExistsError:
                return False
        return True
    finally:
        staged.unlink(missing_ok=True)


def write_json(path: Path, value: dict, *, replace: bool = False) -> bool:
    return write_bytes(path, json_bytes(value), replace=replace)


def load_bus(bus: Path) -> dict:
    bus = bus.resolve(strict=True)
    record = read_json(bus / "bus.json")
    root = record.get("coordination_root")
    if (record.get("schema_version") != 2
            or not re.fullmatch(r"[0-9a-f]{16}", str(record.get("bus_id", "")))
            or not isinstance(root, str) or not Path(root).is_absolute()
            or str(Path(root).resolve(strict=True)) != root):
        raise BusError(f"Invalid bus identity: {bus}")
    return record


def overlaps(first: Path, second: Path) -> bool:
    return first == second or first in second.parents or second in first.parents


def validate_bindings(bus: Path, *, allow_missing_state: bool = False) -> dict:
    """Validate the whole exclusion map, including reused or edited metadata."""
    metadata = bus / "bindings.json"
    if metadata.is_symlink():
        raise BusError("Bindings must be a regular metadata file")
    bindings = read_json(metadata).get("keys")
    if not isinstance(bindings, dict):
        raise BusError("Invalid bindings record")
    state = {"resource": str(bus / "STATE.md"), "kind": "board"}
    if bindings.get("state") != state:
        raise BusError("The state binding must identify this bus board")
    resources = []
    for key, entry in bindings.items():
        identifier(key)
        if key in RESERVED_KEYS or not isinstance(entry, dict):
            raise BusError("Invalid or reserved binding")
        resource = entry.get("resource")
        if (not isinstance(resource, str) or not Path(resource).is_absolute()
                or entry.get("kind") not in {"file", "dir", "build", "board"}):
            raise BusError(f"Invalid binding: {key}")
        path = Path(resource)
        if not (allow_missing_state and key == "state" and not os.path.lexists(path)):
            try:
                canonical = path.resolve(strict=True)
            except (OSError, RuntimeError) as error:
                raise BusError(f"Bound resource unavailable in {bus}: {key} -> {resource}; "
                               "restore its path or coordinate an explicit repair; bindings are frozen") from error
            if str(canonical) != resource or not (path.is_file() or path.is_dir()):
                raise BusError(f"Resource must name an existing canonical file or directory: {key}")
        if key != "state" and overlaps(path, bus):
            raise BusError(f"Binding overlaps bus control files: {key}")
        if any(overlaps(path, other) for other in resources):
            raise BusError(f"Existing bindings overlap: {key}")
        resources.append(path)
    return bindings


@contextmanager
def guard(bus: Path, key: str, agent: str, instance: str):
    """Fail-fast mkdir guard; occupied/ownerless guards are never reclaimed."""
    identifier(key); identifier(agent); identifier(instance)
    directory = bus / "locks" / key
    token = uuid.uuid4().hex
    try:
        directory.mkdir()
    except FileExistsError as error:
        raise BusError(f"Occupied lock: {key}") from error
    created = directory.stat(follow_symlinks=False)
    owner = {"alias": agent, "instance_id": instance, "token_sha256": token_digest(token),
             "utc": utc(), "resource": str(directory), "purpose": "metadata guard"}
    published = False
    refused = False
    try:
        if not write_json(directory / "OWNER", owner):
            refused = True
            raise BusError(f"Foreign OWNER appeared in guard: {key}")
        published = True
        yield
    finally:
        # Clean up only this invocation's directory and metadata. An unsuccessful
        # OWNER write may leave our empty directory; a foreign OWNER stays put.
        # An actual process crash still requires the ordinary recovery procedure.
        try:
            current = directory.stat(follow_symlinks=False)
            if (current.st_dev, current.st_ino) == (created.st_dev, created.st_ino):
                record = directory / "OWNER"
                if record.exists():
                    if not refused and read_json(record) == owner:
                        record.unlink()
                        directory.rmdir()
                elif not published:
                    directory.rmdir()  # succeeds only if our new directory is empty
        except (FileNotFoundError, BusError):
            pass  # Never recover authority from changed or corrupt peer metadata.


def require_participant(bus: Path, agent: str, instance: str) -> dict:
    identifier(agent); identifier(instance)
    participant = read_json(bus / "participants" / f"{agent}.json")
    if participant.get("alias") != agent or participant.get("instance_id") != instance:
        raise BusError("Caller does not match the registered participant instance")
    return participant
