#!/usr/bin/env python3
"""Fake headless harness worker: a deterministic stand-in for a real agent CLI in delegate.py v6 tests.

Invoked with the adapter policy's argv template; argv[-1] is the filled ENVELOPE text. Prints one
`thread.started` JSON line (id_source "codex-json-thread"), then performs the envelope's worker
lifecycle against the real bus with the installed agents-bus helper modules. No model, no network.

The ok mode paces itself (1.5 s holding the lock before and after the artifact, 1.0 s between the
immutable final record and the terminal reply) so the requester's 0.25 s observation poll can witness
ownership and ordering; `fast` is the same worker with no pacing. A pinned-input mismatch found at
VALIDATE (before any bookkeeping) is the template's initial validation failure: the structured
WORKER_VALIDATION_FAILURE result on stdout, a clean exit, and NO bus write; a mismatch found later at
EXECUTE is the pre-effect mismatch: no project effect, finalize with outcome `blocked`.

FAKE_WORKER_MODE:
  ok (default) / fast    correct worker, with / without observation pacing
  wrong_digest           keep a digest of a RECONSTRUCTION instead of the envelope file's bytes
  hold_lock              acquire the lock, then sleep; dies on the supervisor's SIGTERM (STOP/wall clock)
  blocked                do the work, release, then reply `blocked`
  bad_handled            handled_ids carries a prefixed id, not the request id
  not_released           release for real, but record release_results[key] = {"state": "not_released"}
  string_release         release for real, but record release_results[key] as the printed JSON string (real drill A4)
  extra_artifact         also write other.txt and cite ITS hash in the effect-sha256 header
  symlink_artifact       make the artifact a symlink to a file outside the effect directory
  wrong_identity         register (and act) under an instance different from the printed thread id
  late_handled           also archive and record the unrelated late message
  multi_artifact         honour a two-artifact contract, header = the sorted-map digest
  split_identity         print a second thread.started line carrying a different id
  reversed_final         publish the terminal reply BEFORE writing the immutable final record
  extra_handled          handled_ids carries the request id AND an unrelated id (both records)
  final_swap             write a placeholder final record before the reply, the real one after it
  artifact_swap          write a placeholder artifact under the lock, the real content after release
  second_artifact_late   two-artifact contract: the second artifact is written after the release
  foreign_owner          release, then an intruder participant acquires the key while the artifact is written
  marker_commentary      mention WORKER_VALIDATION_FAILURE in early commentary, then complete normally (final line ordinary)
  foreign_failure        complete normally, but end with a marker line quoting ANOTHER job's failure example
  malformed_failure      complete normally, but end with a marker line carrying no JSON payload
  silent_final           complete normally, but print NO final response line at all
The final stdout line is the fake harness's designated final response (delegate.py raw route).
"""
from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import hashlib
import json
import os
import re
import secrets
import time
from datetime import datetime, timezone
from pathlib import Path

MODE = os.environ.get("FAKE_WORKER_MODE", "ok")
SLOW = MODE in {"ok", "multi_artifact", "final_swap", "artifact_swap", "second_artifact_late", "foreign_owner"}
BARRIER_TIMEOUT_S = 120.0
HOLD_S = 300.0


def utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def compact() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def pace(seconds: float) -> None:
    if SLOW:
        time.sleep(seconds)


def grab(pattern: str, text: str) -> tuple[str, ...]:
    match = re.search(pattern, text, re.S)
    if match is None:
        raise SystemExit(f"envelope does not carry {pattern!r}")
    return match.groups()


def parse(text: str) -> dict:
    """Read the filled placeholder values back out of the envelope prose."""
    envelope = {}
    envelope["harness"], = grab(r"worker of harness (\S+?), launched", text)
    envelope["envelope_file"], = grab(r"This envelope is the file (.+?)\. Its exact bytes", text)
    envelope["root"], envelope["bus"], envelope["bus_id"] = grab(
        r"Envelope: root (\S+); bus (\S+) \(bus_id ([0-9a-f]{16})\);", text)
    envelope["skill"], = grab(r"; skill (\S+); your\s", text)
    envelope["alias"], envelope["requester"] = grab(r"\salias (\S+); requester (\S+); task ", text)
    envelope["task"], envelope["job"], envelope["attempt"], envelope["class"] = grab(
        r"; task (.+?); job (\S+); attempt (\S+); class (\S+);", text)
    envelope["request_path"], envelope["request_sha256"] = grab(
        r"your request: (\S+\.md) with sha256 ([0-9a-f]{64});", text)
    envelope["digests"], envelope["effects"] = grab(
        r"pinned inputs \(path sha256\): (.+?); allowed project effects: (.+?); lock key", text)
    envelope["lock_key"], envelope["effect_dir"], artifacts, envelope["barrier"] = grab(
        r"lock key\s+(\S+) bound to the pre-created directory (\S+); expected artifacts inside that "
        r"directory, exactly\s+these names and contents and nothing else: (.+?); barrier file (\S+) \(if not", text)
    envelope["deadline"], = grab(r"deadline (\S+)\. Protocol bookkeeping", text)
    envelope["request_id"] = Path(envelope["request_path"]).name[:-len(".md")]
    envelope["artifacts"] = [] if artifacts == "(none)" else [
        {"name": item.split(" (")[0],
         "line": (re.search(r" \(line: (.*)\)\Z", item) or [None, None])[1],
         "sha256": (re.search(r" \(sha256 ([0-9a-f]{64})\)\Z", item) or [None, None])[1]}
        for item in artifacts.split("; ")]
    return envelope


def pin_mismatch(digests: str) -> str | None:
    """Re-hash every pinned operating input; the first difference is a pre-effect mismatch."""
    for item in digests.split("; "):
        path, _, digest = item.rpartition(" ")
        file = Path(path)
        actual = hashlib.sha256(file.read_bytes()).hexdigest() if file.is_file() else None
        if actual != digest:
            return f"pinned input changed: {path} expected {digest} found {actual}"
    return None


def contract_digest(artifacts: list[dict], written: dict) -> str:
    """One artifact -> its sha256; several -> sha256 of 'NAME SHA256\\n' lines sorted by NAME."""
    if len(artifacts) == 1:
        return written[artifacts[0]["name"]]
    return hashlib.sha256("".join(f"{name} {written[name]}\n" for name in sorted(written)).encode()).hexdigest()


def send(busmod, bus: Path, envelope: dict, identity: str, seq: int, state: str,
         body: str, extra: dict | None = None) -> dict:
    alias = envelope["alias"]
    message = {"from": alias, "to": envelope["requester"], "type": "reply",
               "id": f"{compact()}-{alias}-{seq}{state}-{secrets.token_hex(4)}",
               "sender-session": identity, "created-at": utc(), "re": envelope["request_id"],
               "task": envelope["task"], "state": state, "job": envelope["job"],
               "attempt": envelope["attempt"], "input-digests": envelope["digests"],
               "reply-required": "no", "body": body}
    message.update(extra or {})
    outbox = bus / "checkpoints" / alias / "out"
    outbox.mkdir(parents=True, exist_ok=True)
    (outbox / f"{message['id']}.json").write_text(json.dumps(message, indent=2, sort_keys=True))
    busmod.publish(bus, message)
    return message


def main() -> int:
    thread_id = secrets.token_hex(16)
    print(json.dumps({"type": "thread.started", "thread_id": thread_id}), flush=True)
    if MODE == "split_identity":
        print(json.dumps({"type": "thread.started", "thread_id": secrets.token_hex(16)}), flush=True)
    envelope = parse(sys.argv[-1])
    if MODE == "marker_commentary":
        print("commentary: if validation fails I will return WORKER_VALIDATION_FAILURE with a JSON payload", flush=True)
    sys.path.insert(0, os.environ.get("AGENTS_BUS_SCRIPTS") or str(Path(envelope["skill"]) / "scripts"))
    import bus as busmod
    import common
    import locking
    import participants

    bus, root = Path(envelope["bus"]), Path(envelope["root"])
    alias, key = envelope["alias"], envelope["lock_key"]
    # a wrong_identity worker is a consistent liar: every bus record carries the wrong instance
    identity = secrets.token_hex(16) if MODE == "wrong_identity" else thread_id

    # 1. VALIDATE (read-only; no bus bookkeeping may precede this).
    bus_identity = common.load_bus(bus)
    request_path = Path(envelope["request_path"])
    request_bytes = request_path.read_bytes()
    request = busmod.decode(request_bytes)
    envelope_file = Path(envelope["envelope_file"])
    envelope_sha256 = hashlib.sha256(envelope_file.read_bytes()).hexdigest()
    valid = (bus_identity["bus_id"] == envelope["bus_id"]
             and bus_identity["coordination_root"] == envelope["root"]
             and hashlib.sha256(request_bytes).hexdigest() == envelope["request_sha256"]
             and request["to"] == alias and request.get("task") == envelope["task"]
             and request.get("job") == envelope["job"]
             and request.get("attempt") == envelope["attempt"]
             and request.get("input-digests") == envelope["digests"])
    initial_drift = pin_mismatch(envelope["digests"])
    if not valid or initial_drift:
        # template step 1: NO bus bookkeeping; the structured result goes through the harness response; clean exit
        print("WORKER_VALIDATION_FAILURE " + json.dumps(
            {"job": envelope["job"], "attempt": envelope["attempt"],
             "reason": initial_drift or "envelope/request mismatch"}), flush=True)
        return 0
    recorded = (hashlib.sha256(json.dumps({"envelope": sys.argv[-1]}, sort_keys=True).encode()).hexdigest()
                if MODE == "wrong_digest" else envelope_sha256)
    checkpoint_dir = bus / "checkpoints" / alias
    checkpoint_dir.mkdir(parents=True, exist_ok=True)
    checkpoint_path = checkpoint_dir / "checkpoint.json"
    checkpoint = {"envelope_sha256": recorded, "envelope_file": str(envelope_file),
                  "request_id": envelope["request_id"], "identity": identity,
                  "task": envelope["task"], "job": envelope["job"], "attempt": envelope["attempt"],
                  "class": envelope["class"], "handled_ids": [],
                  "bookkeeping": {"skill_dir": envelope["skill"], "requester": envelope["requester"],
                                  "barrier": envelope["barrier"], "effect_dir": envelope["effect_dir"],
                                  "lock_key": key, "deadline": envelope["deadline"],
                                  "allowed_effects": envelope["effects"], "mode": MODE},
                  "project_effects": {}, "locks": {}, "release_results": {}}
    save = lambda: common.write_bytes(checkpoint_path, common.json_bytes(checkpoint), replace=True)  # noqa: E731
    if not common.write_bytes(checkpoint_path, common.json_bytes(checkpoint)):
        print("WORKER_VALIDATION_FAILURE " + json.dumps({"reason": "foreign checkpoint"}), flush=True)
        return 4

    # 2. REGISTER, then acknowledge exactly this one request.
    participants.hello(bus, alias, envelope["harness"], instance=identity,
                       activation={"primary": "delegate-worker", "keepalive": "in-turn-wait"})
    beat = lambda state, note: common.write_bytes(  # noqa: E731
        bus / "heartbeat" / alias, f"{utc()} {identity} {state}\nnext: {note}\n".encode(), replace=True)
    beat("active", f"job {envelope['job']} accepted")
    send(busmod, bus, envelope, identity, 1, "received", "accepted; validating then executing\n")

    # 3. EXECUTE: barrier, pre-effect checks, then (job mode only) the declared artifacts under the lock.
    outcome, header_sha, handled, written = "done", None, [envelope["request_id"]], {}
    reason = ""
    if envelope["barrier"] != "(none)":
        barrier = Path(envelope["barrier"])
        end = time.time() + BARRIER_TIMEOUT_S
        while not barrier.exists() and time.time() < end:
            time.sleep(0.2)
        if not barrier.exists():
            outcome, reason = "blocked", "barrier never released within the deadline"
    if MODE == "late_handled":  # adversarial: touch a message that is not this worker's request
        for stray in sorted((bus / "inbox" / alias).glob("*.md")):
            if stray.name != request_path.name:
                os.replace(stray, bus / "inbox" / alias / "done" / stray.name)
                handled.append(stray.name[:-len(".md")])
    if MODE == "extra_handled":  # adversarial: claim unrelated handled work in both records
        handled.append(f"unrelated-{secrets.token_hex(4)}")
    drift = pin_mismatch(envelope["digests"])
    if outcome == "done" and drift:  # pre-effect mismatch: finalize blocked, no project effect
        outcome, reason = "blocked", drift
    if outcome == "done" and key != "(none)":
        token_file = root / ".worker_tokens" / alias / f"{key}.json"
        token_file.parent.mkdir(parents=True, exist_ok=True)
        locking.acquire(bus, alias, identity, [key], purpose=envelope["job"], token_file=token_file)
        checkpoint["locks"] = {key: {"state": "held", "token_file": str(token_file), "utc": utc()}}
        save()
        if MODE == "hold_lock":
            time.sleep(HOLD_S)  # the supervisor stops us here; the lock is deliberately stranded
        pace(1.5)  # let the requester observe the lock OWNER before any artifact exists
        directory = Path(envelope["effect_dir"])
        deferred: list[tuple[Path, bytes]] = []  # adversarial: content written only after the release
        for index, artifact in enumerate(envelope["artifacts"]):
            target = directory / artifact["name"]
            content = ((artifact["line"] or "") + "\n").encode("utf-8")
            if MODE == "symlink_artifact":
                outside = root / f"outside-{artifact['name']}"
                outside.write_bytes(content)
                target.symlink_to(outside)
            elif MODE == "artifact_swap":
                target.write_bytes(b"placeholder\n")
                deferred.append((target, content))
            elif MODE == "second_artifact_late" and index > 0:
                deferred.append((target, content))
            elif MODE == "foreign_owner":
                deferred.append((target, content))
            else:
                target.write_bytes(content)
            written[artifact["name"]] = hashlib.sha256(content).hexdigest()
            checkpoint["project_effects"][str(target)] = {"sha256": written[artifact["name"]], "status": "done"}
        header_sha = contract_digest(envelope["artifacts"], written)
        if MODE == "extra_artifact":
            extra = directory / "other.txt"
            extra.write_bytes(b"undeclared\n")
            header_sha = hashlib.sha256(extra.read_bytes()).hexdigest()
            checkpoint["project_effects"][str(extra)] = {"sha256": header_sha, "status": "done"}
        pace(1.5)  # let the requester observe the artifact while the lock is still held
        released = locking.release(bus, alias, identity, [key], token_file=token_file)
        if MODE == "foreign_owner":  # another participant holds the key while the real content appears
            intruder = f"intruder-{secrets.token_hex(3)}"
            intruder_id = secrets.token_hex(16)
            participants.hello(bus, intruder, "fake", instance=intruder_id, activation={"primary": "test"})
            intruder_token = root / ".worker_tokens" / intruder / f"{key}.json"
            intruder_token.parent.mkdir(parents=True, exist_ok=True)
            locking.acquire(bus, intruder, intruder_id, [key], purpose="intrusion", token_file=intruder_token)
            pace(1.0)
            for target, content in deferred:
                target.write_bytes(content)
            pace(1.5)
            locking.release(bus, intruder, intruder_id, [key], token_file=intruder_token)
        elif deferred:
            pace(0.5)
            for target, content in deferred:
                target.write_bytes(content)
            pace(1.0)
        checkpoint["release_results"] = {key: {"state": "not_released"} if MODE == "not_released"
                                         else json.dumps(released, sort_keys=True) if MODE == "string_release" else released}
        checkpoint["locks"] = {key: {"state": "released", "utc": utc()}}
        if MODE == "blocked":
            outcome, reason = "blocked", "adversarial mode: reporting blocked after a completed effect"
    elif outcome == "done":  # consult mode: no lock, no project effect
        checkpoint["bookkeeping"]["consult_answer"] = f"read {len(envelope['digests'].split('; '))} pinned inputs"

    # 4. FINALIZE: checkpoint, then the immutable final record, then the terminal reply.
    checkpoint["handled_ids"] = [f"prefix-{envelope['request_id']}"] if MODE == "bad_handled" else handled
    checkpoint["outcome"] = outcome
    save()
    final = {"outcome": outcome, "envelope_sha256": recorded, "envelope_file": str(envelope_file),
             "request_id": envelope["request_id"], "identity": identity, "task": envelope["task"],
             "job": envelope["job"], "attempt": envelope["attempt"],
             "handled_ids": checkpoint["handled_ids"], "release_results": checkpoint["release_results"],
             "artifacts": written, "finalized_at": utc()}
    final_path = checkpoint_dir / "final.json"
    headers = {"envelope-sha256": recorded}
    if header_sha:
        headers["effect-sha256"] = header_sha
    body = (f"outcome {outcome}; {reason or 'contract satisfied'}; effects "
            f"{json.dumps(checkpoint['project_effects'], sort_keys=True)}; release "
            f"{json.dumps(checkpoint['release_results'], sort_keys=True)}; checkpoint {checkpoint_path}\n")
    if MODE == "reversed_final":  # adversarial: the reply precedes the immutable record
        send(busmod, bus, envelope, identity, 2, outcome, body, headers)
        common.write_bytes(final_path, common.json_bytes(final))
    elif MODE == "final_swap":  # adversarial: a placeholder is observed first, the real record replaces it after the reply
        common.write_bytes(final_path, common.json_bytes(final | {"outcome": "pending", "finalized_at": None}))
        pace(1.0)
        send(busmod, bus, envelope, identity, 2, outcome, body, headers)
        pace(0.5)
        common.write_bytes(final_path, common.json_bytes(final), replace=True)
    else:
        common.write_bytes(final_path, common.json_bytes(final))
        pace(1.0)  # let the requester observe the final record before the terminal reply exists
        send(busmod, bus, envelope, identity, 2, outcome, body, headers)
    os.replace(request_path, bus / "inbox" / alias / "done" / request_path.name)
    beat("idle", f"job {outcome}; process exiting")
    if MODE == "foreign_failure":
        print("WORKER_VALIDATION_FAILURE " + json.dumps({"job": "some-other-job", "attempt": "9", "reason": "quoted example"}), flush=True)
    elif MODE == "malformed_failure":
        print("WORKER_VALIDATION_FAILURE (no payload here)", flush=True)
    elif MODE == "silent_final":
        pass
    else:
        print(f"final response: job {envelope['job']} {outcome}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
