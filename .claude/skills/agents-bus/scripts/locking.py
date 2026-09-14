"""Exact resource bindings and token-checked, fail-fast resource locks."""
from __future__ import annotations

import json
import hmac
from pathlib import Path
import uuid

from common import (BusError, RESERVED_KEYS, guard, identifier, load_bus, overlaps,
                    read_json, require_participant, token_digest, utc, validate_bindings,
                    write_bytes, write_json)


def _keys(keys: list[str]) -> list[str]:
    if not keys or len(set(keys)) != len(keys):
        raise BusError("Provide a nonempty list of distinct keys")
    for key in keys:
        identifier(key)
        if key in RESERVED_KEYS:
            raise BusError(f"Internal guard key is reserved: {key}")
    return sorted(keys)


def _bindings(bus: Path) -> dict:
    return validate_bindings(bus)


def _claims(bus: Path, resources: list[Path]) -> None:
    """Respect all existing claims; aliases in other registries are not identity.

    Recognizes the existing coordinate skill's array of {agent, files, since}.
    Unknown formats fail conservatively and require the caller to reconcile.
    No registry is ever written, expired or treated as an atomic bus lock.
    """
    root = Path(load_bus(bus)["coordination_root"])
    for directory in (".Codex", ".claude"):
        registry = root / directory / "coordination.json"
        if not registry.exists():
            continue
        try:
            claims = json.loads(registry.read_text())
        except (OSError, ValueError) as error:
            raise BusError(f"Unreadable claim registry: {registry}") from error
        if not isinstance(claims, list):
            raise BusError(f"Unsupported claim registry; reconcile it first: {registry}")
        for claim in claims:
            if (not isinstance(claim, dict) or not isinstance(claim.get("agent"), str)
                    or not isinstance(claim.get("files"), list)
                    or not all(isinstance(name, str) for name in claim["files"])):
                raise BusError(f"Malformed claim registry: {registry}")
            for name in claim["files"]:
                if any(character in name for character in "*?["):
                    raise BusError(f"Unsupported glob claim; reconcile first: {name}")
                claimed = (root / name).resolve()
                if any(overlaps(resource, claimed) for resource in resources):
                    raise BusError(f"Resource claimed by {claim['agent']}: {claimed}")


def _log(bus: Path, agent: str, instance: str, line: str) -> dict:
    """Board writes are separate from committed binding/lock effects."""
    try:
        with guard(bus, "meta", agent, instance):
            with guard(bus, "state", agent, instance):
                board = bus / "STATE.md"
                write_bytes(board, (board.read_text() + f"\n- {utc()} {line}\n").encode(),
                            replace=True)
        return {"board_update_pending": False}
    except (OSError, BusError, UnicodeError) as error:
        return {"board_update_pending": True, "board_update_error": str(error),
                "board_update": line}


def bind(bus: Path, agent: str, instance: str, key: str, resource: Path,
         *, kind: str | None = None) -> dict:
    bus = bus.resolve(strict=True); load_bus(bus); require_participant(bus, agent, instance)
    identifier(key)
    if key in RESERVED_KEYS | {"state"}:
        raise BusError(f"Reserved binding key: {key}")
    try:
        resource = resource.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise BusError(f"Cannot bind unavailable resource: {key} -> {resource}") from error
    if not (resource.is_file() or resource.is_dir()):
        raise BusError(f"Binding requires a regular file or directory: {key} -> {resource}")
    if overlaps(bus, resource):
        raise BusError("Bus control files and their ancestors cannot be user resources")
    kind = kind or ("dir" if resource.is_dir() else "file")
    if kind not in {"file", "dir", "build", "board"}:
        raise BusError("Unsupported resource kind")
    entry = {"resource": str(resource), "kind": kind}
    with guard(bus, "meta", agent, instance):
        bindings = _bindings(bus)
        if key in bindings:
            if bindings[key] != entry:
                raise BusError("Established bindings are frozen")
            return {"state": "unchanged", "key": key, **entry}
        if (bus / "locks" / key).exists():
            raise BusError("Cannot bind an occupied key")
        if any(overlaps(resource, Path(value["resource"])) for value in bindings.values()):
            raise BusError("Resource overlaps an existing binding")
        bindings[key] = entry
        write_json(bus / "bindings.json", {"keys": bindings}, replace=True)
    return {"state": "bound", "key": key, **entry,
            **_log(bus, agent, instance, f"{agent} bound {key} to {resource}")}


def acquire(bus: Path, agent: str, instance: str, keys: list[str], *,
            purpose: str, token_file: Path) -> dict:
    bus = bus.resolve(strict=True); identity = load_bus(bus)
    require_participant(bus, agent, instance); keys = _keys(keys)
    if not isinstance(purpose, str) or not purpose.strip():
        raise BusError("A lock purpose is required")
    token_file = token_file.resolve()
    if bus == token_file or bus in token_file.parents:
        raise BusError("The new token bundle must live outside the bus")
    if token_file.exists():
        raise BusError("Token bundle already exists; use a new path, or release with that bundle")
    created: list[str] = []
    with guard(bus, "meta", agent, instance):
        bindings = _bindings(bus)
        if any(key not in bindings for key in keys):
            raise BusError("Unbound key; use bind explicitly first")
        _claims(bus, [Path(bindings[key]["resource"]) for key in keys])
        tokens = {key: uuid.uuid4().hex for key in keys}
        owners = {key: {"alias": agent, "instance_id": instance, "token_sha256": token_digest(tokens[key]),
                        "utc": utc(), "resource": bindings[key]["resource"], "purpose": purpose}
                  for key in keys}
        bundle = {"bus_id": identity["bus_id"], "alias": agent, "instance_id": instance,
                  "keys": tokens}
        # Persist the capability before any resource ownership can survive us.
        if not write_json(token_file, bundle):
            raise BusError("Token bundle path was concurrently occupied")
        try:
            for key in keys:
                directory = bus / "locks" / key
                try:
                    directory.mkdir()
                except FileExistsError as error:
                    raise BusError(f"Occupied lock: {key}; retry later with a new token-bundle path") from error
                created.append(key)
                if not write_json(directory / "OWNER", owners[key]):
                    raise BusError(f"Unexpected existing OWNER: {key}")
        except (OSError, ValueError):
            for key in reversed(created):
                directory = bus / "locks" / key
                owner = directory / "OWNER"
                if owner.exists():
                    if read_json(owner) != owners[key]:
                        continue
                    owner.unlink()
                directory.rmdir()
            raise
    return {"state": "acquired", "keys": keys, "token_file": str(token_file)}


def release(bus: Path, agent: str, instance: str, keys: list[str], *, token_file: Path) -> dict:
    bus = bus.resolve(strict=True); identity = load_bus(bus)
    require_participant(bus, agent, instance); keys = _keys(keys)
    try:
        token_file = token_file.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise BusError(f"Token bundle unavailable: {token_file}") from error
    if bus == token_file or bus in token_file.parents:
        raise BusError("Token bundle must be caller-owned outside the bus")
    bundle = read_json(token_file)
    if (bundle.get("bus_id") != identity["bus_id"] or bundle.get("alias") != agent
            or bundle.get("instance_id") != instance or not isinstance(bundle.get("keys"), dict)
            or any(not isinstance(bundle["keys"].get(key), str) for key in keys)):
        raise BusError("Token bundle does not match this caller, bus and key set")
    with guard(bus, "meta", agent, instance):
        # The owner check AND removal serialize against acquire and another release.
        existing: list[Path] = []
        not_held = []
        for key in keys:
            directory = bus / "locks" / key
            if not directory.exists():
                not_held.append(key)
                continue  # An exact duplicate release with no successor is harmless.
            owner = read_json(directory / "OWNER")
            if (owner.get("alias") != agent or owner.get("instance_id") != instance
                    or not isinstance(owner.get("token_sha256"), str)
                    or not hmac.compare_digest(owner["token_sha256"], token_digest(bundle["keys"][key]))):
                raise BusError(f"Wrong owner or token: {key}")
            existing.append(directory)
        for directory in reversed(existing):
            (directory / "OWNER").unlink()
            directory.rmdir()
    return {"state": "released" if existing else "not_held", "keys": keys,
            "released": [directory.name for directory in existing], "not_held": not_held}


def show(bus: Path) -> list[dict]:
    bus = bus.resolve(strict=True); load_bus(bus)
    result = []
    for directory in sorted((bus / "locks").iterdir()):
        if not directory.is_dir():
            continue
        try:
            owner = read_json(directory / "OWNER")
        except BusError:
            owner = None
        if owner is not None:
            # Public status exposes only diagnostic metadata, never a raw token,
            # even if a legacy or externally written OWNER contains one.
            owner = {key: owner[key] for key in
                     ("alias", "instance_id", "utc", "resource", "purpose", "token_sha256")
                     if key in owner}
        result.append({"key": directory.name, "owner": owner, "occupied": True})
    return result
