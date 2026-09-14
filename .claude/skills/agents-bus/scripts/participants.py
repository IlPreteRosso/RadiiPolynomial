"""Same-instance participant registration for the isolated universal-bus prototype.

Activation is descriptive data. This module never starts a watcher, worker, or
scheduler. A successful registration can leave a deferred board update, which is
reported explicitly and retried by repeating ``hello`` with the returned id.
"""
from __future__ import annotations

import json
from pathlib import Path
import uuid

import common


def _activation(value: dict | None, *, previous: dict | None = None) -> dict:
    value = {} if value is None else value
    previous = {} if previous is None else previous
    if not isinstance(value, dict) or not isinstance(previous, dict):
        raise common.BusError("Activation must be an object containing inert data")
    try:
        # Copy the caller's mutable input and reject non-JSON execution objects.
        # Merge before applying defaults: a partial refresh does not erase other
        # recorded capabilities. Supplied top-level fields replace those fields.
        result = json.loads(json.dumps({**previous, **value}, allow_nan=False))
    except (TypeError, ValueError) as error:
        raise common.BusError(f"Activation is not JSON data: {error}") from error
    result.setdefault("primary", "user-relay")
    result.setdefault("keepalive", "unknown")
    return result


def _board_update(bus: Path, participant: dict, refreshed: bool) -> None:
    """Append within the exact alias section; never rewrite existing prose."""
    agent, instance = participant["alias"], participant["instance_id"]
    # Serialize against ordinary resource acquisition/release as well as other
    # board writers. Both guards fail immediately; there is no wait while locked.
    with common.guard(bus, "meta", agent, instance):
        with common.guard(bus, "state", agent, instance):
            board = bus / "STATE.md"
            previous = board.read_bytes().decode("utf-8")
            heading = f"## {agent}"
            lines = previous.splitlines(keepends=True)
            section = next((index for index, line in enumerate(lines)
                            if line.rstrip("\r\n") == heading), None)
            end = len(lines)
            if section is not None:
                end = next((index for index in range(section + 1, len(lines))
                            if lines[index].startswith(("## ", "##\t"))
                            or lines[index].rstrip("\r\n") == "##"), end)
            before, after = "".join(lines[:end]), "".join(lines[end:])
            separator = "" if before.endswith(("\n\n", "\r\n\r\n")) else "\n" if before.endswith("\n") else "\n\n"
            addition = f"{heading}\n\n" if section is None else ""
            action = "Refreshed registration for" if refreshed else "Registered"
            addition += (f"- {participant['last_seen']}: {action} `{agent}` as `{instance}` "
                         f"({participant['harness']}); activation is descriptive only.\n")
            if after:
                addition += "\n"
            common.write_bytes(board, (before + separator + addition + after).encode(), replace=True)


def hello(bus: Path, agent: str, harness: str, *, instance: str | None = None,
          activation: dict | None = None) -> dict:
    """Register or refresh an explicitly owned instance; never replace an alias.

    The returned participant fields include ``board_update_pending`` and
    ``heartbeat_update_pending``. A true pending flag means the registration is
    already durable; its corresponding error describes the secondary write that
    must be retried using this same instance id. No owner token is returned.
    Omitting ``instance`` always mints a fresh id, never adopting shared state.
    Omitting ``activation`` on a refresh preserves that instance's recorded data.
    A partial activation object updates only its supplied top-level fields.
    """
    common.identifier(agent)
    if not isinstance(harness, str) or not harness.strip() or "\n" in harness or "\r" in harness:
        raise common.BusError("Harness must be a nonempty single-line name")
    instance = uuid.uuid4().hex[:16] if instance is None else common.identifier(instance)
    advertised_activation = _activation(activation)
    bus = Path(bus).resolve(strict=True)
    common.load_bus(bus)
    participant_file = bus / "participants" / f"{agent}.json"
    heartbeat_error = None
    with common.guard(bus, "participants", agent, instance):
        refreshed = participant_file.exists()
        now = common.utc()
        if refreshed:
            participant = common.read_json(participant_file)
            if (participant.get("alias") != agent
                    or participant.get("instance_id") != instance):
                raise common.BusError("Alias belongs to another instance; use a new alias")
            if participant.get("generation") != 0:
                raise common.BusError("Unsupported participant generation; replacement is not implemented")
            if participant.get("harness") != harness:
                raise common.BusError("A same-instance refresh cannot change its harness")
            if not isinstance(participant.get("registered_at"), str):
                raise common.BusError("Participant record has no registration timestamp")
            advertised_activation = _activation(activation, previous=participant.get("activation"))
            participant = {**participant, "last_seen": now,
                           "activation": advertised_activation}
        else:
            participant = {"alias": agent, "harness": harness,
                           "instance_id": instance, "generation": 0,
                           "activation": advertised_activation,
                           "registered_at": now, "last_seen": now}
        (bus / "inbox" / agent / "done").mkdir(parents=True, exist_ok=True)
        if not common.write_json(participant_file, participant, replace=refreshed):
            # A protocol-external writer cannot be silently overwritten.
            raise common.BusError("Participant publication lost to another writer; inspect the record")
        try:
            common.write_bytes(bus / "heartbeat" / agent,
                               f"{now} {instance} active\nnext: registration complete\n".encode(),
                               replace=True)
        except (common.BusError, OSError) as error:
            heartbeat_error = str(error)

    result = dict(participant)
    result["heartbeat_update_pending"] = heartbeat_error is not None
    if heartbeat_error is not None:
        result["heartbeat_update_error"] = heartbeat_error
    try:
        _board_update(bus, participant, refreshed)
    except (common.BusError, OSError, UnicodeError) as error:
        result["board_update_pending"] = True
        result["board_update_error"] = str(error)
    else:
        result["board_update_pending"] = False
    return result
