"""Delegation adapter (design §6.2): launch ONE fresh headless worker of another harness for ONE
bounded job, as a NEW bus participant. stdlib only; imports the co-located bus helpers.

Guarantees and limits (read before use):
- Never resumes a transcript, never substitutes for the live peer; launches only what the caller's
  LOCAL adapter policy names, under caps reserved atomically at launch.
- One writer per record: PLAN.json, REQUEST.bytes, STATE.json (guarded transitions), SUPERVISOR.json +
  LAUNCH.json (launch = the only process that may stop the child, via the STOP file), BIND.json / WAIT.json
  (sealed only on completion; pending observations live in *.pending.json and OBSERVATIONS.jsonl),
  RESULT.json (verify, read-only otherwise), REPLAY.json (replay, gated and revalidated).
- Evidence classes in RESULT: verified (requester-observed SNAPSHOT or requester-computed consistency),
  failed, and UNVERIFIED (a predicate this adapter cannot establish from its own observations). Every
  observation is digest-bound to the bytes verified later; a changed or contradictory binding FAILS, a
  missing one is UNVERIFIED. Polling never proves continuous ownership or durability: the predicates
  are named as snapshots (artifact content seen while the bound worker's OWNER bracketed the read; final
  record digest seen with no terminal record in `.messages` after the snapshot). Worker-written records
  are consistency checks only. Process exit (`outcome`) and the worker's task result (`task_outcome`,
  e.g. validation_failed) are separate fields.
- Cessation is verified for the child's process group only; escaped descendants are not covered.
Subcommands: plan, publish, launch, bind, wait, verify, replay. Exit status: 0 = the documented success
(plan/publish done, launch outcome ok, bound, terminal reply, contract PASS, replay idempotent); 2 = a
bus/adapter refusal or a pending result; 3 = verify PASS-WITH-UNVERIFIED; 1 = every other non-success.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import secrets
import signal
import subprocess
import sys
import time
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

import bus as busmod
import common

PLACEHOLDER = re.compile(r"<[A-Z_]+>")
ALLOWED_ARGV_PLACEHOLDERS = {"<EXE>", "<ROOT>", "<RUN_DIR>", "<BUS>", "<WORKER_INSTANCE>", "<ENVELOPE>"}
FORBIDDEN_PREFIXES = ("--resume", "--continue", "--dangerously", "--fork", "--last", "--bypass", "--approve-for-me", "--full-auto", "--worktree")
FORBIDDEN_TOKENS = {"resume", "fork", "continue", "-r", "-c", "--last"}
LEDGER_STATES = {"reserved", "starting", "running", "unknown", "ended"}
LAUNCH_FLOOR_S = 5
ENV_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
BASE_ENV_NAMES = ("PATH", "HOME", "LANG")
FIXED_ENV_NAMES = {"AGENTS_BUS", "PYTHONDONTWRITEBYTECODE"}
OBSERVE_POLL_S = 0.25
PIN_DEFAULT = ("SKILL.md", "references/RECOVERY.md", "scripts/bus.py", "scripts/admin.py", "scripts/common.py",
               "scripts/locking.py", "scripts/participants.py", "scripts/bootstrap.py")


class DelegateError(common.BusError):
    pass


def utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def compact() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def parse_utc(value: str | None) -> datetime | None:
    if not value:
        return None
    value = value.strip().replace("+00:00", "Z")
    for fmt in ("%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S.%fZ", "%Y%m%dT%H%M%SZ"):
        try:
            return datetime.strptime(value, fmt).replace(tzinfo=timezone.utc)
        except ValueError:
            continue
    return None


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_once(path: Path, value: dict) -> None:
    if not common.write_bytes(path, common.json_bytes(value)):
        raise DelegateError(f"record exists: {path}")


def replace_json(path: Path, value: dict) -> None:
    common.write_bytes(path, common.json_bytes(value), replace=True)


def journal(run_dir: Path, event: str, **fields) -> None:
    """Append-only requester observation journal (monotonic requester clock + UTC)."""
    line = json.dumps({"event": event, "t": time.monotonic(), "utc": utc(), **fields}, sort_keys=True)
    with open(run_dir / "OBSERVATIONS.jsonl", "a", encoding="utf-8") as stream:
        stream.write(line + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def read_journal(run_dir: Path) -> list[dict]:
    path = run_dir / "OBSERVATIONS.jsonl"
    if not path.exists():
        return []
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        with contextlib.suppress(ValueError):
            out.append(json.loads(line))
    return out


@contextlib.contextmanager
def txn(directory: Path, name: str = ".txn"):
    guard = directory / name
    try:
        guard.mkdir()
    except FileExistsError as error:
        raise DelegateError(f"concurrent transition in progress: {guard}") from error
    try:
        yield
    finally:
        with contextlib.suppress(OSError):
            guard.rmdir()


def annotate(run_dir: Path, **fields) -> dict:
    with txn(run_dir):
        state = common.read_json(run_dir / "STATE.json")
        state.update(fields)
        replace_json(run_dir / "STATE.json", state)
        return state


def transition(run_dir: Path, expected: set[str], new: str, **fields) -> dict:
    with txn(run_dir):
        state = common.read_json(run_dir / "STATE.json")
        if state.get("state") not in expected:
            raise DelegateError(f"state {state.get('state')!r} not in {sorted(expected)}")
        state.update(fields)
        state["state"] = new
        state.setdefault("history", []).append({"state": new, "at": utc()})
        replace_json(run_dir / "STATE.json", state)
        return state


# ----------------------------------------------------------------------------- policy

def _option_values(argv: list[str], option: str) -> list[str]:
    values = []
    for i, item in enumerate(argv):
        if item == option and i + 1 < len(argv):
            values.append(argv[i + 1])
        elif item.startswith(option + "="):
            values.append(item.split("=", 1)[1])
    return values


def load_policy(path: Path) -> dict:
    policy = common.read_json(path)
    allowed_env = policy.get("env_allowlist", [])
    if (not isinstance(allowed_env, list)
            or any(not isinstance(name, str) or not ENV_NAME.fullmatch(name)
                   for name in allowed_env)):
        raise DelegateError("env_allowlist must be a list of explicit environment variable names")
    if len(set(allowed_env)) != len(allowed_env):
        raise DelegateError("env_allowlist must not contain duplicate names")
    if set(allowed_env) & FIXED_ENV_NAMES:
        raise DelegateError("AGENTS_BUS and PYTHONDONTWRITEBYTECODE are fixed by the launcher")
    policy["env_allowlist"] = allowed_env
    for key in ("harness", "executable", "argv_template", "id_source", "wall_clock_s", "max_per_hour", "max_concurrent", "classes"):
        if key not in policy:
            raise DelegateError(f"Adapter policy lacks {key!r}")
    harness = policy["harness"]
    if harness not in {"codex", "claude"}:
        raise DelegateError("harness must be codex or claude")
    if policy["id_source"] not in {"codex-json-thread", "claude-stream-json-session"}:
        raise DelegateError("Unsupported id_source")
    if (harness == "codex") != (policy["id_source"] == "codex-json-thread"):
        raise DelegateError("id_source must match the harness")
    exe = policy["executable"]
    if not isinstance(exe, str) or not Path(exe).is_absolute():
        raise DelegateError("Adapter executable must be an absolute path")
    argv = policy["argv_template"]
    if not isinstance(argv, list) or not argv or any(not isinstance(a, str) for a in argv):
        raise DelegateError("argv_template must be a non-empty list of strings")
    if argv[0] != "<EXE>" or argv.count("<ENVELOPE>") != 1 or argv[-1] != "<ENVELOPE>":
        raise DelegateError("argv_template must start with <EXE> and end with exactly one <ENVELOPE> argument")
    for item in argv[1:-1]:
        low = item.lower()
        if low in FORBIDDEN_TOKENS or any(low.startswith(p) for p in FORBIDDEN_PREFIXES):
            raise DelegateError(f"argv_template contains a forbidden mode, alias or bypass: {item}")
        for ph in PLACEHOLDER.findall(item):
            if ph not in ALLOWED_ARGV_PLACEHOLDERS:
                raise DelegateError(f"unknown argv placeholder {ph}")
    def single(option: str, allowed: set[str] | None = None, required: bool = True) -> str | None:
        values = _option_values(argv, option)
        if len(values) > 1:
            raise DelegateError(f"duplicate option {option}")
        if not values:
            if required:
                raise DelegateError(f"argv_template must pass {option}")
            return None
        if allowed is not None and values[0] not in allowed:
            raise DelegateError(f"unsupported value for {option}: {values[0]}")
        return values[0]
    if harness == "codex":
        single("--sandbox", {"read-only", "workspace-write"})
        single("--ask-for-approval", {"never"})
        if argv[1:-1].count("--json") != 1 or any(a.startswith("--json=") for a in argv[1:-1]):
            raise DelegateError("codex argv_template must pass the bare flag --json exactly once (identity is bound from its thread.started event)")
        if "exec" not in argv[1:-1]:
            raise DelegateError("codex argv_template must use the exec subcommand")
    else:
        if "-p" not in argv[1:-1] and "--print" not in argv[1:-1]:
            raise DelegateError("claude argv_template must use -p/--print")
        single("--output-format", {"stream-json"})
        single("--permission-mode", {"dontAsk"})
        if single("--session-id") != "<WORKER_INSTANCE>":
            raise DelegateError("claude argv_template must pass --session-id <WORKER_INSTANCE>")
    for key in ("wall_clock_s", "max_per_hour", "max_concurrent"):
        if not isinstance(policy[key], int) or isinstance(policy[key], bool) or policy[key] <= 0:
            raise DelegateError(f"{key} must be a positive integer")
    if policy["wall_clock_s"] <= LAUNCH_FLOOR_S:
        raise DelegateError(f"wall_clock_s must exceed the launch floor of {LAUNCH_FLOOR_S} s")
    if not isinstance(policy["classes"], list) or not set(policy["classes"]) <= {"consult", "job"}:
        raise DelegateError("classes must be a subset of consult, job")
    runner = policy.get("runner_argv", ["python3"])
    if not isinstance(runner, list) or any(not isinstance(a, str) for a in runner):
        raise DelegateError("runner_argv must be a list of strings")
    policy["runner_argv"] = runner
    return policy


def worker_environment(policy: dict, bus: str, parent: dict[str, str]) -> dict[str, str]:
    """Filter a launch-time snapshot using a validated policy; never persist values.

    This limits accidental inheritance, not access to credentials in HOME or
    other readable files. Explicitly allowed variables may themselves be secrets.
    The names recorded by the supervisor describe what Popen receives; a child
    runtime may subsequently add or change variables.
    """
    names = set(BASE_ENV_NAMES) | set(policy["env_allowlist"])
    env = {name: parent[name] for name in names if name in parent}
    env["AGENTS_BUS"] = bus
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


# ----------------------------------------------------------------------------- capacity ledger

def ledger_dir(root: Path) -> Path:
    return root / ".adapter" / "launch"


def _valid_ledger(record: dict) -> bool:
    return (isinstance(record.get("job_id"), str) and isinstance(record.get("attempt_id"), str)
            and isinstance(record.get("run_dir"), str) and record.get("ledger_state") in LEDGER_STATES
            and isinstance(record.get("launched_epoch"), (int, float)))


def ledger_scan(root: Path, now: float) -> tuple[int, int, list[str]]:
    """Conservative accounting: corrupt, unsupported or incomplete records count as live AND recent."""
    recent = live = 0
    notes = []
    for record_path in sorted(ledger_dir(root).glob("*.json")):
        try:
            record = common.read_json(record_path)
        except common.BusError:
            live += 1; recent += 1
            notes.append(f"corrupt record counted live+recent: {record_path.name}")
            continue
        if not _valid_ledger(record):
            live += 1; recent += 1
            notes.append(f"unsupported/incomplete record counted live+recent: {record_path.name}")
            continue
        if now - record["launched_epoch"] < 3600:
            recent += 1
        if record["ledger_state"] != "ended":
            live += 1
    return recent, live, notes


def ledger_reserve(root: Path, policy: dict, job: str, attempt: str, run_dir: Path) -> Path:
    directory = ledger_dir(root)
    directory.mkdir(parents=True, exist_ok=True)
    with txn(directory, ".ledger-txn"):
        now = time.time()
        recent, live, notes = ledger_scan(root, now)
        if recent >= policy["max_per_hour"]:
            raise DelegateError("Adapter policy max_per_hour reached")
        if live >= policy["max_concurrent"]:
            raise DelegateError("Adapter policy max_concurrent reached (reserved/starting/running/unknown/unsupported records count)")
        record_path = directory / f"{job}.{attempt}.json"
        write_once(record_path, {"job_id": job, "attempt_id": attempt, "run_dir": str(run_dir), "ledger_state": "reserved",
                                 "reserved_at": utc(), "launched_epoch": now, "scan_notes": notes})
        return record_path


def ledger_update(record_path: Path, **fields) -> None:
    with txn(record_path.parent, ".ledger-txn"):
        record = common.read_json(record_path)
        record.update(fields)
        replace_json(record_path, record)


# ----------------------------------------------------------------------------- artifacts

def artifact_header_digest(expected: list[dict]) -> str:
    """Value the worker must put in `effect-sha256`: one artifact -> its sha256; several -> the digest of the
    canonical map 'name sha256\\n' sorted by name."""
    if len(expected) == 1:
        return expected[0]["sha256"]
    return sha256_bytes("".join(f"{e['name']} {e['sha256']}\n" for e in sorted(expected, key=lambda e: e["name"])).encode("utf-8"))


# ----------------------------------------------------------------------------- plan / publish

def plan(args: argparse.Namespace) -> dict:
    bus = Path(args.bus).resolve(strict=True)
    identity = common.load_bus(bus)
    root = Path(identity["coordination_root"])
    policy_path = Path(args.policy).resolve(strict=True)
    policy = load_policy(policy_path)
    worker_class = args.worker_class
    if worker_class not in policy["classes"]:
        raise DelegateError(f"class {worker_class!r} not allowed by the adapter policy")
    if worker_class == "consult" and (args.lock_key or args.effect_dir or args.expect):
        raise DelegateError("class consult takes no lock, effect directory or artifact contract (design §6.5.3)")
    if worker_class == "job" and not (args.lock_key and args.effect_dir and args.expect):
        raise DelegateError("class job needs --lock-key, --effect-dir and at least one --expect artifact")
    run_dir = Path(args.run_dir).resolve()
    if bus == run_dir or bus in run_dir.parents:
        raise DelegateError("run_dir must live outside the bus")
    common.require_participant(bus, args.agent, args.instance)
    job = common.identifier(args.job)
    attempt = common.identifier(args.attempt)
    skill_dir = Path(args.skill_dir).resolve(strict=True)
    template_path = Path(args.template).resolve(strict=True)
    pinned: dict[str, str] = {}
    for rel in PIN_DEFAULT:
        p = skill_dir / rel
        if not p.is_file():
            raise DelegateError(f"required operating input missing: {p}")
        pinned[str(p)] = sha256_file(p)
    protocol = bus / "PROTOCOL.md"
    if not protocol.is_file():
        raise DelegateError("bus PROTOCOL.md missing")
    pinned[str(protocol)] = sha256_file(protocol)
    pinned[str(template_path)] = sha256_file(template_path)
    for item in args.pin or []:
        p = Path(item).resolve(strict=True)
        pinned[str(p)] = sha256_file(p)
    input_digests = "; ".join(f"{k} {v}" for k, v in sorted(pinned.items()))
    effect_dir = Path(args.effect_dir).resolve() if args.effect_dir else None
    expected_artifacts: list[dict] = []
    seen = set()
    for spec in args.expect or []:
        name, _, cond = spec.partition("=")
        if "/" in name or name in {"", ".", ".."} or name in seen:
            raise DelegateError("artifact names are unique bare file names inside the effect directory")
        seen.add(name)
        entry = {"name": name}
        if cond.startswith("sha256:") and re.fullmatch(r"[0-9a-f]{64}", cond[7:]):
            entry["sha256"] = cond[7:]
        elif cond.startswith("line:") and cond[5:] and "\n" not in cond[5:]:
            entry["sha256"] = sha256_bytes((cond[5:] + "\n").encode("utf-8"))
            entry["line"] = cond[5:]
        else:
            raise DelegateError("every artifact needs a condition: NAME=sha256:<64 hex> or NAME=line:<text> (name-only contracts are not supported)")
        expected_artifacts.append(entry)
    if args.lock_key:
        bindings = common.read_json(bus / "bindings.json").get("keys", {})
        if args.lock_key not in bindings:
            raise DelegateError("lock key must be bound by the maintainer before dispatch (design §6.2.9)")
        if effect_dir is None or str(effect_dir) != bindings[args.lock_key]["resource"]:
            raise DelegateError("effect_dir must equal the bound resource of lock_key")
        if not effect_dir.is_dir() or effect_dir.is_symlink():
            raise DelegateError("effect_dir must be an existing real directory")
        pre = sorted(p.name for p in effect_dir.iterdir())
        if pre:
            raise DelegateError(f"effect_dir must be empty before dispatch: {pre}")
    alias = f"{policy['harness']}-worker-{secrets.token_hex(4)}"
    expected_identity = str(uuid.uuid4()) if policy["harness"] == "claude" else None
    limit_s = min(int(args.deadline_s), policy["wall_clock_s"])
    deadline_utc = (datetime.now(timezone.utc) + timedelta(seconds=limit_s)).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_dir.mkdir(parents=True, exist_ok=False)
    request_id = f"{compact()}-{args.agent}-req-{job}-{secrets.token_hex(4)}"
    request = {"from": args.agent, "to": alias, "type": "request", "id": request_id, "sender-session": args.instance,
               "created-at": utc(), "task": args.task, "job": job, "attempt": attempt, "class": worker_class,
               "target-reason": args.target_reason, "input-digests": input_digests,
               "deadline": f"{deadline_utc}; default: blocked reply, no lock change", "reply-required": "yes",
               "body": Path(args.request_body).read_text(encoding="utf-8")}
    if args.delegated_from:
        request["delegated-from"] = args.delegated_from
    request_bytes = busmod.encode(request)
    request_sha = sha256_bytes(request_bytes)
    envelope_path = run_dir / "ENVELOPE.txt"
    effect_header = artifact_header_digest(expected_artifacts) if expected_artifacts else "(none)"
    fill = {"<HARNESS>": policy["harness"], "<ROOT>": str(root), "<BUS>": str(bus), "<BUS_ID>": identity["bus_id"],
            "<SKILL_DIR>": str(skill_dir), "<WORKER_ALIAS>": alias, "<REQUESTER_ALIAS>": args.agent, "<TASK>": args.task,
            "<JOB_ID>": job, "<ATTEMPT_ID>": attempt, "<WORKER_CLASS>": worker_class, "<WORKER_REQUEST_ID>": request_id,
            "<WORKER_REQUEST_SHA256>": request_sha, "<INPUT_DIGESTS>": input_digests,
            "<ALLOWED_EFFECTS>": args.allowed_effects, "<LOCK_KEY>": args.lock_key or "(none)",
            "<EFFECT_DIR>": str(effect_dir) if effect_dir else "(none)",
            "<EXPECTED_ARTIFACTS>": "; ".join(f"{e['name']}" + (f" (line: {e['line']})" if "line" in e else f" (sha256 {e['sha256']})") for e in expected_artifacts) or "(none)",
            "<EFFECT_HEADER_RULE>": ("the sha256 of that single artifact" if len(expected_artifacts) == 1 else
                                     "the sha256 of the text made of one line per artifact, 'NAME SHA256' followed by a newline, sorted by NAME") if expected_artifacts else "(no artifact: omit the header)",
            "<BARRIER_PATH>": args.barrier or "(none)", "<SUPERVISOR_DEADLINE>": deadline_utc,
            "<RUNNER_ARGV>": " ".join(policy["runner_argv"]), "<WORKER_INSTANCE>": expected_identity or "(harness-provided: CODEX_THREAD_ID)",
            "<ENVELOPE_FILE>": str(envelope_path)}
    text = template_path.read_text(encoding="utf-8")
    for key, value in fill.items():
        text = text.replace(key, value)
    leftover = sorted(set(PLACEHOLDER.findall(text)))
    if leftover:
        raise DelegateError(f"Unfilled template placeholders: {leftover}")
    envelope_bytes = text.encode("utf-8")
    if not common.write_bytes(envelope_path, envelope_bytes):
        raise DelegateError("envelope file exists")
    argv = []
    for item in policy["argv_template"]:
        argv.append("<ENVELOPE bytes>" if item == "<ENVELOPE>" else item.replace("<EXE>", policy["executable"]).replace("<ROOT>", str(root))
                    .replace("<RUN_DIR>", str(run_dir)).replace("<BUS>", str(bus)).replace("<WORKER_INSTANCE>", expected_identity or ""))
    plan_record = {
        "adapter": "delegate.py v6", "bus_id": identity["bus_id"], "coordination_root": str(root), "bus": str(bus),
        "job_id": job, "attempt_id": attempt, "task": args.task, "class": worker_class, "target_reason": args.target_reason,
        "delegated_from": args.delegated_from, "worker_alias": alias, "worker_harness": policy["harness"], "id_source": policy["id_source"],
        "expected_identity": expected_identity, "requester": {"alias": args.agent, "instance": args.instance},
        "pinned_inputs": pinned, "input_digests": input_digests, "allowed_effects": args.allowed_effects, "lock_key": args.lock_key,
        "effect_dir": str(effect_dir) if effect_dir else None, "expected_artifacts": expected_artifacts, "expected_effect_header": effect_header,
        "barrier": args.barrier, "limit_s": limit_s, "deadline_utc": deadline_utc, "policy_path": str(policy_path), "policy_sha256": sha256_file(policy_path),
        "executable": policy["executable"], "effective_argv": argv, "worker_request_id": request_id, "worker_request_sha256": request_sha,
        "envelope_path": str(envelope_path), "envelope_sha256": sha256_bytes(envelope_bytes), "template_path": str(template_path),
        "template_sha256": sha256_file(template_path), "run_dir": str(run_dir), "prepared_at": utc(),
    }
    (run_dir / "REQUEST.bytes").write_bytes(request_bytes)
    write_once(run_dir / "PLAN.json", plan_record)
    write_once(run_dir / "STATE.json", {"state": "prepared", "history": [{"state": "prepared", "at": utc()}]})
    journal(run_dir, "prepared", request_id=request_id, envelope_sha256=plan_record["envelope_sha256"])
    return publish(argparse.Namespace(run_dir=str(run_dir))) | {"worker_alias": alias, "envelope_sha256": plan_record["envelope_sha256"], "limit_s": limit_s}


def _validated_request(run_dir: Path, planrec: dict) -> dict:
    """Read REQUEST.bytes once; refuse unless that exact buffer is the immutable plan's request (digest, id, recipient)."""
    buf = (run_dir / "REQUEST.bytes").read_bytes()
    if sha256_bytes(buf) != planrec["worker_request_sha256"]:
        raise DelegateError("REQUEST.bytes differ from the prepared request digest; nothing published")
    request = busmod.decode(buf)
    request.pop("path", None)
    if request.get("id") != planrec["worker_request_id"] or request.get("to") != planrec["worker_alias"]:
        raise DelegateError("REQUEST.bytes carry a different id or recipient than the plan; nothing published")
    return request


def publish(args: argparse.Namespace) -> dict:
    """Idempotent continuation: publish the prepared request bytes (same id, same bytes) and seal `published`."""
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    state = common.read_json(run_dir / "STATE.json").get("state")
    if state == "published":
        return {"state": "published", "run_dir": str(run_dir), "worker_request_id": planrec["worker_request_id"], "note": "already published"}
    if state != "prepared":
        raise DelegateError(f"publish needs state prepared, found {state!r}")
    bus = Path(planrec["bus"])
    request = _validated_request(run_dir, planrec)  # the exact buffer that was hashed is the one published
    busmod.publish(bus, request)
    stored = bus / ".messages" / f"{planrec['worker_request_id']}.md"
    if sha256_file(stored) != planrec["worker_request_sha256"]:
        raise DelegateError("published request bytes differ from the prepared bytes")
    transition(run_dir, {"prepared"}, "published", published_at=utc())
    journal(run_dir, "published", request_id=planrec["worker_request_id"])
    return {"state": "published", "run_dir": str(run_dir), "worker_request_id": planrec["worker_request_id"]}


# ----------------------------------------------------------------------------- supervision

def group_state(pgid: int) -> tuple[str, list[str] | str]:
    try:
        result = subprocess.run(["pgrep", "-g", str(pgid)], capture_output=True, text=True, timeout=5)
    except (OSError, subprocess.TimeoutExpired) as error:
        return "unknown", f"pgrep-error:{error!r}"
    if result.returncode == 0:
        return "alive", result.stdout.split()
    if result.returncode == 1:
        return "none", []
    return "unknown", f"pgrep-rc={result.returncode} stderr={result.stderr.strip()}"


def kill_group(pgid: int, sup: dict) -> str:
    """Bounded TERM/KILL of the child's group. Never raises; returns 'none' | 'alive' | 'unknown' | 'signal-error'."""
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
            sup.setdefault("group_signals", []).append(f"{sig.name}@{utc()}")
        except ProcessLookupError:
            sup.setdefault("group_signals", []).append(f"{sig.name}:no-such-group@{utc()}")
            return "none"
        except OSError as error:
            sup.setdefault("group_signals", []).append(f"{sig.name}:error {error!r}@{utc()}")
            return "signal-error"
        end = time.monotonic() + 3
        while time.monotonic() < end:
            state = group_state(pgid)[0]
            if state == "none":
                return "none"
            time.sleep(0.2)
    return group_state(pgid)[0]


def launch(args: argparse.Namespace, report: dict | None = None) -> dict:
    """`report` (optional, caller-owned) receives `persistence_errors` even when the final record itself could not be written."""
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    policy_path = Path(planrec["policy_path"])
    if sha256_file(policy_path) != planrec["policy_sha256"]:
        raise DelegateError("adapter policy changed since plan; re-plan")
    policy = load_policy(policy_path)
    envelope_bytes = Path(planrec["envelope_path"]).read_bytes()
    if sha256_bytes(envelope_bytes) != planrec["envelope_sha256"]:
        raise DelegateError("envelope bytes changed since plan")
    env = worker_environment(policy, planrec["bus"], dict(os.environ))
    remaining = (parse_utc(planrec["deadline_utc"]) - datetime.now(timezone.utc)).total_seconds()
    if remaining <= LAUNCH_FLOOR_S:
        transition(run_dir, {"published"}, "ended", outcome="deadline-expired-before-launch")
        return {"state": "deadline-expired-before-launch"}
    limit_s = int(min(remaining, planrec["limit_s"], policy["wall_clock_s"]))
    root = Path(planrec["coordination_root"])
    transition(run_dir, {"published"}, "starting")
    sup = {"supervisor": "delegate.py v6", "job": planrec["job_id"], "attempt": planrec["attempt_id"], "limit_s": limit_s,
           "argv_redacted": planrec["effective_argv"], "envelope_sha256": planrec["envelope_sha256"], "cwd": str(root),
           "started_at": utc(), "spawned": "unknown", "cessation_scope": "process group (PGID) only; escaped descendants not covered",
           "environment_names": sorted(env), "environment_policy_allowlist": policy["env_allowlist"],
           "environment_scope": "names passed at spawn; values are not recorded; child runtime may change its environment",
           "deadline_anchor": "monotonic clock at reservation; setup and record writes count against limit_s"}
    child = None
    pgid = None
    stopped = killed = False
    out = err = None
    cleanup_error = None
    persistence_errors: list[str] = []
    try:
        ledger_path = ledger_reserve(root, policy, planrec["job_id"], planrec["attempt_id"], run_dir)
    except DelegateError:
        transition(run_dir, {"starting"}, "published", note="capacity reservation refused; run stays launchable")
        raise
    # --- from here the reserved attempt is bracketed: every exit path persists a final supervisor + ledger record
    deadline = time.monotonic() + limit_s
    try:
        annotate(run_dir, ledger=str(ledger_path))
        write_once(run_dir / "SUPERVISOR.json", sup)
        out = open(run_dir / "stdout.log", "xb")
        err = open(run_dir / "stderr.log", "xb")
        argv = [a if a != "<ENVELOPE bytes>" else envelope_bytes.decode("utf-8") for a in planrec["effective_argv"]]
        try:
            child = subprocess.Popen(argv, cwd=str(root), stdin=subprocess.DEVNULL, stdout=out, stderr=err, env=env, start_new_session=True)
        except OSError as error:
            sup.update(spawned=False, launcher_error=repr(error), outcome="launcher-failed", cessation_verified=True)
            return {"state": "launcher-failed", "error": repr(error)}
        pgid = child.pid
        sup.update(spawned=True, pid=child.pid, pgid=pgid, launched_at=utc())
        replace_json(run_dir / "SUPERVISOR.json", sup)
        write_once(run_dir / "LAUNCH.json", {"pid": child.pid, "pgid": pgid, "launched_at": sup["launched_at"], "limit_s": limit_s})
        ledger_update(ledger_path, ledger_state="running", pid=child.pid, pgid=pgid, launched_epoch=time.time())
        transition(run_dir, {"starting"}, "running", pid=child.pid, pgid=pgid)
        journal(run_dir, "spawned", pid=child.pid)
        stop_file = run_dir / "STOP"
        while child.poll() is None:
            if stop_file.exists():
                stopped = True
                sup["stop_requested_at"] = utc()
                sup["stop_result"] = kill_group(pgid, sup)
                break
            if time.monotonic() > deadline:
                killed = True
                sup["timeout_hit_at"] = utc()
                sup["timeout_kill_result"] = kill_group(pgid, sup)
                break
            time.sleep(0.25)
        try:
            rc = child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            kill_group(pgid, sup)
            try:
                rc = child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                rc = None
        sup.update(direct_child_exit_code=rc, killed_by_supervisor=killed, stopped_by_request=stopped, direct_child_ended_at=utc())
        with contextlib.suppress(OSError):
            for stream in (out, err):
                stream.flush()
        sup.update(_task_result(run_dir, planrec))
        return {"state": "pending-finalization"}  # replaced in finally
    except BaseException as error:
        sup["supervisor_exception"] = repr(error)
        raise
    finally:
        try:
            for stream in (out, err):
                if stream is not None:
                    with contextlib.suppress(OSError):
                        stream.close()
            if child is not None and child.poll() is None:
                kill_group(pgid, sup)
                with contextlib.suppress(Exception):
                    child.wait(timeout=5)
            if pgid is not None:
                state, detail = group_state(pgid)
                sup["group_state_after_child_exit"] = {"state": state, "detail": detail}
                if state != "none":
                    kill_group(pgid, sup)
                state2, detail2 = group_state(pgid)
                sup["group_state_final"] = {"state": state2, "detail": detail2}
                sup["cessation_verified"] = state2 == "none"
                sup["cessation_unknown"] = state2 != "none"
                rc = sup.get("direct_child_exit_code")
                if "supervisor_exception" in sup:
                    sup["outcome"] = "supervisor-error"
                else:
                    sup["outcome"] = ("stopped" if stopped else "timeout" if killed else "ok" if rc == 0 and sup["cessation_verified"]
                                      else "nonzero-exit" if rc not in (0, None) else "cessation-not-verified")
            elif sup.get("spawned") == "unknown":
                sup.update(spawned=False, outcome="setup-failed", cessation_verified=True)
            sup["ended_at"] = utc()
        except BaseException as error:  # never lose the record over a cleanup failure
            cleanup_error = repr(error)
            sup["cleanup_error"] = cleanup_error
            sup["outcome"] = "cleanup-unknown"
            sup["cessation_verified"] = False
            sup["ended_at"] = utc()
        sup.setdefault("task_outcome", "unclassified")
        certain = sup.get("cessation_verified") is True and sup.get("outcome") not in {"cleanup-unknown", "supervisor-error"}
        # Persistence order: the durable final supervisor record, then STATE and the journal, then the ledger LAST.
        # The ledger becomes `ended` only when every prior record was durably written; any earlier failure leaves it
        # `unknown` (capacity retained until an explicit reconciliation) and a failed ledger write leaves it as it was.
        for label, action in (("SUPERVISOR.json", lambda: replace_json(run_dir / "SUPERVISOR.json", sup)),
                              ("STATE.json", lambda: transition(run_dir, {"starting", "running"}, "ended", outcome=sup.get("outcome"))),
                              ("journal", lambda: journal(run_dir, "ended", outcome=sup.get("outcome"), cessation_verified=sup.get("cessation_verified")))):
            try:
                action()
            except BaseException as error:  # storage failure: keep going, report the uncertainty, retain capacity
                persistence_errors.append(f"{label}: {error!r}")
        try:
            ledger_update(ledger_path, ledger_state=("ended" if certain and not persistence_errors else "unknown"), outcome=sup.get("outcome"),
                          ended_at=sup.get("ended_at"), **({"persistence_errors": list(persistence_errors)} if persistence_errors else {}))
        except BaseException as error:
            persistence_errors.append(f"ledger: {error!r}")
        if persistence_errors:
            sup["persistence_errors"] = persistence_errors
            sup["finalization"] = "unresolved: final records not fully persisted; capacity retained; verification blocked until reconciled"
            if report is not None:
                report["persistence_errors"] = list(persistence_errors)
            for fallback in (lambda: replace_json(run_dir / "SUPERVISOR.json", sup),
                             lambda: replace_json(run_dir / "PERSISTENCE_ERRORS.json", {"persistence_errors": persistence_errors, "at": utc()})):
                with contextlib.suppress(BaseException):
                    fallback()
            print(json.dumps({"warning": "final records not fully persisted; capacity stays reserved until reconciled", "errors": persistence_errors}), file=sys.stderr)
    # unreachable: every path returns inside try or raises


VALIDATION_MARKER = "WORKER_VALIDATION_FAILURE"


def _final_response(run_dir: Path, planrec: dict) -> tuple[str | None, str]:
    """The DESIGNATED final harness response: the `-o` last-message file when the policy names one; else the last
    completed agent message of a `--json` event stream; else (explicit raw route, fake harness) the last non-JSON
    stdout line. Commentary elsewhere in the stream is never a result."""
    for a in planrec.get("effective_argv", []):
        if a.endswith("last_message.txt"):
            path = Path(a)
            if path.is_file():
                try:
                    return path.read_text(encoding="utf-8", errors="replace"), "last-message-file"
                except OSError:
                    return None, "last-message-file-unreadable"
            return None, "last-message-file-missing"
    stdout = run_dir / "stdout.log"
    if not stdout.is_file():
        return None, "no-stdout"
    last_agent = None
    last_raw = None
    with contextlib.suppress(OSError):
        for line in stdout.read_text(encoding="utf-8", errors="replace").splitlines():
            line = line.strip()
            if not line:
                continue
            if line.startswith("{"):
                with contextlib.suppress(ValueError):
                    event = json.loads(line)
                    item = event.get("item") if isinstance(event, dict) else None
                    if isinstance(item, dict) and item.get("type") == "agent_message" and isinstance(item.get("text"), str) and event.get("type") == "item.completed":
                        last_agent = item["text"]
                continue
            last_raw = line
    if last_agent is not None:
        return last_agent, "json-agent-message"
    if last_raw is not None:
        return last_raw, "raw-last-line"
    return None, "no-final-response"


def _task_result(run_dir: Path, planrec: dict) -> dict:
    """Classify the worker's task result from the designated final response only.
    validation_failed = the response STARTS with the marker and carries a JSON object whose job/attempt equal
    this run's; inconclusive = the marker is at the result boundary but the payload is malformed or belongs to
    another job/attempt, OR the designated response is unavailable / unreadable / empty (never a success label);
    unclassified = an ordinary non-empty response (mentions elsewhere in commentary never count)."""
    text, source = _final_response(run_dir, planrec)
    if text is None or not text.strip():
        return {"task_outcome": "inconclusive", "task_result_source": source,
                "task_result": {"why": "designated final response unavailable or empty" + ("" if text is None else " (blank output)")}}
    stripped = text.strip()
    if not stripped.startswith(VALIDATION_MARKER):
        return {"task_outcome": "unclassified", "task_result_source": source}
    payload = stripped[len(VALIDATION_MARKER):].strip()
    detail = None
    with contextlib.suppress(ValueError):
        detail = json.loads(payload)
    if not isinstance(detail, dict) or not isinstance(detail.get("reason"), str):
        return {"task_outcome": "inconclusive", "task_result_source": source, "task_result": {"raw": stripped[:500], "why": "malformed payload"}}
    if detail.get("job") != planrec["job_id"] or detail.get("attempt") != planrec["attempt_id"]:
        return {"task_outcome": "inconclusive", "task_result_source": source, "task_result": {"raw": stripped[:500], "why": "job/attempt do not correlate with this run"}}
    return {"task_outcome": "validation_failed", "task_result_source": source, "task_result": {k: detail[k] for k in ("job", "attempt", "reason")}}


def _launch_result_wrapper(args: argparse.Namespace) -> dict:
    report: dict = {}
    result = launch(args, report)
    errors = report.get("persistence_errors") or []
    if result.get("state") == "pending-finalization":
        sup = {}
        with contextlib.suppress(common.BusError, OSError):
            sup = common.read_json(Path(args.run_dir).resolve() / "SUPERVISOR.json")
        errors = errors or sup.get("persistence_errors") or []
        result = {"state": sup.get("outcome", "record-unreadable"), "exit_code": sup.get("direct_child_exit_code"), "cessation_verified": sup.get("cessation_verified"),
                  "task_outcome": sup.get("task_outcome")}
    return result | ({"persistence_errors": errors} if errors else {})


# ----------------------------------------------------------------------------- identity

def observed_identity(run_dir: Path, id_source: str) -> tuple[str | None, list[str]]:
    """All identity-bearing events in the harness output; the identity is valid only if they agree."""
    path = run_dir / "stdout.log"
    found: list[str] = []
    if path.exists():
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if id_source == "codex-json-thread" and event.get("type") == "thread.started" and isinstance(event.get("thread_id"), str):
                found.append(event["thread_id"])
            if id_source == "claude-stream-json-session" and isinstance(event.get("session_id"), str):
                found.append(event["session_id"])
    distinct = sorted(set(found))
    return (distinct[0] if len(distinct) == 1 else None), found


def bind(args: argparse.Namespace) -> dict:
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    if (run_dir / "BIND.json").exists():
        return common.read_json(run_dir / "BIND.json") | {"note": "already bound"}
    bus = Path(planrec["bus"])
    end = time.monotonic() + float(args.timeout)
    observed = hello = None
    events: list[str] = []
    not_launched = previous = None
    while time.monotonic() < end:
        observed, events = observed_identity(run_dir, planrec["id_source"])
        participant = bus / "participants" / f"{planrec['worker_alias']}.json"
        if observed and participant.exists():
            with contextlib.suppress(common.BusError):
                hello = common.read_json(participant)
            if hello and hello.get("instance_id") == observed:
                break
        previous, not_launched = not_launched, _not_launched(run_dir)
        if not_launched and not_launched == previous:
            break  # seen on two consecutive polls: no launch is under way; the caller must relaunch before binding
        time.sleep(1)
    expected = planrec.get("expected_identity")
    bound = bool(observed and hello and hello.get("instance_id") == observed and (expected is None or observed == expected))
    record = {"observed_identity": observed, "identity_events": events, "hello_instance": (hello or {}).get("instance_id"),
              "expected_identity": expected, "bound": bound, "observed_at": utc()}
    if bound:
        write_once(run_dir / "BIND.json", record | {"note": "provisional; verify re-checks after completion"})
        journal(run_dir, "bound", identity=observed)
    else:
        note = f"pending: {not_launched}" if not_launched else "pending: not bound within the timeout; rerun bind"
        replace_json(run_dir / "BIND.pending.json", record | {"note": note})
        journal(run_dir, "bind-pending", observed=observed, events=len(events), not_launched=not_launched)
    return {"bound": bound, "observed_identity": observed, "hello_instance": record["hello_instance"],
            **({"not_launched": not_launched} if not_launched else {})}


def _not_launched(run_dir: Path) -> str | None:
    """A reason string when no worker can appear for this run without a new launch; None while a launch may be under way."""
    with contextlib.suppress(common.BusError, OSError):
        state = common.read_json(run_dir / "STATE.json")
        history = [h.get("state") for h in state.get("history", []) if isinstance(h, dict)]
        if state.get("state") == "ended":
            return f"run ended before binding (outcome={state.get('outcome')!r})"
        refused_at = parse_utc(state["history"][-1].get("at")) if state.get("history") else None
        if (state.get("state") == "published" and history[-2:] == ["starting", "published"] and refused_at is not None
                and (datetime.now(timezone.utc) - refused_at).total_seconds() > LAUNCH_FLOOR_S):
            # A launch transitions to `starting` within milliseconds of being invoked; a refusal older than the
            # launch floor, still unchanged one poll later, means nothing is launching.
            return f"launch refused, run stays launchable ({state.get('note')!r}); relaunch before binding"
    return None


# ----------------------------------------------------------------------------- wait (observing)

def _owner_now(bus: Path, key: str | None) -> dict | None:
    """The lock OWNER record at this instant (identity fields only), or None when absent/unreadable."""
    if not key:
        return None
    try:
        owner = common.read_json(bus / "locks" / key / "OWNER")
    except common.BusError:
        return None
    return {k: owner.get(k) for k in ("alias", "instance_id", "token_sha256", "resource", "utc")}


def _terminal_in_store(bus: Path, alias: str, request_id: str) -> bool:
    """Any terminal reply for this request anywhere in the immutable store (delivered, archived or staged)."""
    for path in sorted((bus / ".messages").glob("*.md")):
        if path.name.startswith("."):
            continue
        try:
            message = busmod.decode(path.read_bytes())
        except (OSError, ValueError):
            continue
        if message.get("from") == alias and message.get("re") == request_id and message.get("state") in {"done", "blocked"}:
            return True
    return False


def _observe_once(run_dir: Path, planrec: dict, seen: dict, identity: str) -> None:
    """Requester-side observations of worker-visible state; each first sighting is journaled once, digest-bound.

    lock-held-observed: the OWNER carrying the worker alias + bound identity (its token digest is remembered).
    artifact-observed: the artifact's bytes hashed between two OWNER reads; `held_by_bound_worker` is true only
    when both reads show the worker alias, the bound identity and the remembered token digest.
    final-record-observed: the record's bytes hashed FIRST, then the whole `.messages` store scanned for a
    terminal reply to this request; `terminal_absent_after_snapshot` names exactly that check.
    """
    bus = Path(planrec["bus"])
    alias = planrec["worker_alias"]
    key = planrec.get("lock_key")
    if key:
        owner = _owner_now(bus, key)
        if owner is not None:
            if owner.get("alias") == alias and owner.get("instance_id") == identity and "lock-held" not in seen:
                seen["lock-held"] = True
                seen["lock-token"] = owner.get("token_sha256")
                journal(run_dir, "lock-held-observed", key=key, owner=owner)
        elif "lock-held" in seen and "lock-released" not in seen:
            seen["lock-released"] = True
            journal(run_dir, "lock-absent-after-hold-observed", key=key)
    final_path = bus / "checkpoints" / alias / "final.json"
    if final_path.exists() and "final" not in seen:
        with contextlib.suppress(OSError):
            digest = sha256_bytes(final_path.read_bytes())
            absent = not _terminal_in_store(bus, alias, planrec["worker_request_id"])
            seen["final"] = True
            seen["final-sha256"] = digest
            journal(run_dir, "final-record-observed", sha256=digest, terminal_absent_after_snapshot=absent,
                    terminal_already_present=(not absent), absence_namespace=".messages (whole immutable store)")
    if planrec.get("effect_dir"):
        for e in planrec["expected_artifacts"]:
            p = Path(planrec["effect_dir"]) / e["name"]
            if p.exists() and ("artifact:" + e["name"]) not in seen:
                seen["artifact:" + e["name"]] = True
                with contextlib.suppress(OSError):
                    before = _owner_now(bus, key)
                    digest = sha256_bytes(p.read_bytes()) if p.is_file() and not p.is_symlink() else None
                    after = _owner_now(bus, key)
                    def bound(o: dict | None) -> bool:
                        return bool(o) and o.get("alias") == alias and o.get("instance_id") == identity and o.get("token_sha256") == seen.get("lock-token") and seen.get("lock-token") is not None
                    journal(run_dir, "artifact-observed", name=e["name"], sha256=digest, expected_sha256=e["sha256"],
                            owner_before=before, owner_after=after, held_by_bound_worker=bound(before) and bound(after))


def wait(args: argparse.Namespace) -> dict:
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    if (run_dir / "WAIT.json").exists():
        rec = common.read_json(run_dir / "WAIT.json")
        return {"terminal": rec.get("terminal_state"), "id": rec.get("terminal_id"), "receipts": len(rec.get("receipts", [])), "note": "already sealed"}
    if not (run_dir / "BIND.json").exists():
        raise DelegateError("identity not bound; refuse to trust replies (design §6.2.3)")
    bindrec = common.read_json(run_dir / "BIND.json")
    identity = bindrec["observed_identity"]
    bus = Path(planrec["bus"])
    pending_path = run_dir / "WAIT.pending.json"
    previous = common.read_json(pending_path) if pending_path.exists() else {}
    handled: list[str] = list(previous.get("handled", []))
    receipts: list[dict] = list(previous.get("receipts", []))
    seen: dict = dict(previous.get("seen", {}))
    end = time.monotonic() + float(args.timeout_s)
    headers = {"job": planrec["job_id"], "attempt": planrec["attempt_id"]}
    terminal = None
    while time.monotonic() < end and terminal is None:
        _observe_once(run_dir, planrec, seen, identity)
        matches = busmod.wait(bus, planrec["requester"]["alias"], planrec["worker_request_id"], OBSERVE_POLL_S, task=planrec["task"],
                              exclude_ids=tuple(handled), sender=planrec["worker_alias"], sender_session=identity, expected_headers=headers)
        for message in matches:
            if message.get("state") in {"done", "blocked"}:
                terminal = message
                _observe_once(run_dir, planrec, seen, identity)
                final_now = None
                with contextlib.suppress(OSError):
                    fp = bus / "checkpoints" / planrec["worker_alias"] / "final.json"
                    final_now = sha256_bytes(fp.read_bytes()) if fp.exists() else None
                journal(run_dir, "terminal-observed", id=message["id"], state=message.get("state"), final_record_seen_before=("final" in seen),
                        final_sha256_now=final_now, lock_absent_now=(not (bus / "locks" / planrec["lock_key"]).exists()) if planrec.get("lock_key") else None)
                break
            if message["id"] not in handled:
                handled.append(message["id"])
                receipts.append({k: v for k, v in message.items() if k != "body"})
                journal(run_dir, "receipt-observed", id=message["id"], state=message.get("state"))
        if terminal is None:
            replace_json(pending_path, {"handled": handled, "receipts": receipts, "seen": seen, "updated_at": utc()})
    if terminal is None:
        replace_json(pending_path, {"handled": handled, "receipts": receipts, "seen": seen, "updated_at": utc(), "note": "pending: no terminal reply within the timeout; rerun wait"})
        journal(run_dir, "wait-pending")
        return {"terminal": None, "id": None, "receipts": len(receipts)}
    record = {"receipts": receipts, "terminal_id": terminal["id"], "terminal_state": terminal.get("state"), "seen": seen, "sealed_at": utc()}
    write_once(run_dir / "WAIT.json", record)
    return {"terminal": record["terminal_state"], "id": record["terminal_id"], "receipts": len(receipts)}


# ----------------------------------------------------------------------------- verify (read-only)

def _real_inside(path: Path, directory: Path) -> bool:
    try:
        return not path.is_symlink() and path.is_file() and path.resolve(strict=True).parent == directory.resolve(strict=True)
    except OSError:
        return False


def verify(args: argparse.Namespace) -> dict:
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    bus = Path(planrec["bus"])
    alias = planrec["worker_alias"]
    checks: list[dict] = []

    def check(name: str, ok: bool, **detail):
        checks.append({"check": name, "status": "verified" if ok else "failed", **detail})

    def unverified(name: str, **detail):
        checks.append({"check": name, "status": "unverified", **detail})

    sup = common.read_json(run_dir / "SUPERVISOR.json")
    check("supervisor outcome ok (process exit)", sup.get("outcome") == "ok", outcome=sup.get("outcome"), exit_code=sup.get("direct_child_exit_code"))
    check("worker task result is neither a validation failure nor inconclusive (designated final response)", sup.get("task_outcome") == "unclassified",
          task_outcome=sup.get("task_outcome"), task_result=sup.get("task_result"), source=sup.get("task_result_source"))
    check("process-group cessation verified (scope: PGID only)", sup.get("cessation_verified") is True)
    # launch finalization must be resolved: no persistence errors anywhere and the ledger record durably `ended`
    state_rec = common.read_json(run_dir / "STATE.json")
    ledger = {}
    with contextlib.suppress(common.BusError, OSError, TypeError):
        ledger = common.read_json(Path(state_rec.get("ledger")))
    fallback_errors = {}
    with contextlib.suppress(common.BusError):
        fallback_errors = common.read_json(run_dir / "PERSISTENCE_ERRORS.json")
    check("launch finalization resolved (no persistence errors; ledger record ended; run state ended)",
          not sup.get("persistence_errors") and not fallback_errors.get("persistence_errors") and ledger.get("ledger_state") == "ended" and state_rec.get("state") == "ended",
          persistence_errors=sup.get("persistence_errors") or fallback_errors.get("persistence_errors"), ledger_state=ledger.get("ledger_state"), run_state=state_rec.get("state"))
    envelope_path = Path(planrec["envelope_path"])
    envelope_now = sha256_file(envelope_path) if envelope_path.is_file() and not envelope_path.is_symlink() else None
    check("envelope file present as a regular file with the plan's digest", envelope_now == planrec["envelope_sha256"], now=envelope_now, expected=planrec["envelope_sha256"])
    bindrec = common.read_json(run_dir / "BIND.json") if (run_dir / "BIND.json").exists() else {}
    observed_final, events = observed_identity(run_dir, planrec["id_source"])
    identity = bindrec.get("observed_identity")
    check("identity: harness output carries exactly one identity, equal to the provisional binding", bool(identity) and observed_final == identity, events=events, bound=identity)
    participant = {}
    with contextlib.suppress(common.BusError):
        participant = common.read_json(bus / "participants" / f"{alias}.json")
    check("identity: hello instance == observed", participant.get("instance_id") == identity)
    if planrec.get("expected_identity"):
        check("identity: expected (argv --session-id) == observed", planrec["expected_identity"] == identity)
    waitrec = common.read_json(run_dir / "WAIT.json") if (run_dir / "WAIT.json").exists() else {}
    terminal = {}
    tid = waitrec.get("terminal_id")
    tpath = bus / ".messages" / f"{tid}.md" if tid else None
    if tpath and tpath.exists():
        terminal = busmod.decode(tpath.read_bytes())
    check("terminal reply exists in the immutable store", bool(terminal), id=tid)
    check("terminal reply is done", terminal.get("state") == "done", state=terminal.get("state"))
    exact = {"from": alias, "to": planrec["requester"]["alias"], "type": "reply", "re": planrec["worker_request_id"], "task": planrec["task"],
             "job": planrec["job_id"], "attempt": planrec["attempt_id"], "sender-session": identity, "input-digests": planrec["input_digests"]}
    check("terminal reply exact correlation headers (incl. input-digests)", all(terminal.get(k) == v for k, v in exact.items()), expected=exact)
    check("terminal reply envelope-sha256 header == plan", terminal.get("envelope-sha256") == planrec["envelope_sha256"])
    # pinned inputs: snapshot still intact at verification time (what the worker read is its own claim)
    drift = {k: (sha256_file(Path(k)) if Path(k).is_file() else None) for k in planrec["pinned_inputs"]}
    check("pinned operating inputs unchanged since plan (verified snapshot, not a claim about execution-time reads)",
          all(drift[k] == v for k, v in planrec["pinned_inputs"].items()), drifted=[k for k, v in planrec["pinned_inputs"].items() if drift[k] != v])
    stored = bus / ".messages" / f"{planrec['worker_request_id']}.md"
    archived = bus / "inbox" / alias / "done" / f"{planrec['worker_request_id']}.md"
    prepared = (run_dir / "REQUEST.bytes").read_bytes()
    check("request bytes: prepared digest == plan", sha256_bytes(prepared) == planrec["worker_request_sha256"])
    check("request bytes: stored == prepared", stored.exists() and stored.read_bytes() == prepared)
    check("request archived by the worker (identical bytes)", archived.exists() and archived.read_bytes() == prepared)
    check("request no longer pending in the worker inbox", not (bus / "inbox" / alias / f"{planrec['worker_request_id']}.md").exists())
    cp_path = bus / "checkpoints" / alias / "checkpoint.json"
    cp = {}
    with contextlib.suppress(common.BusError):
        cp = common.read_json(cp_path)
    check("worker checkpoint present", bool(cp), path=str(cp_path))
    check("checkpoint envelope_sha256 == plan (worker hashed the envelope FILE)", cp.get("envelope_sha256") == planrec["envelope_sha256"], recorded=cp.get("envelope_sha256"))
    check("checkpoint envelope_file == plan", cp.get("envelope_file") == planrec["envelope_path"])
    check("checkpoint identity == observed", cp.get("identity") == identity)
    for k, pk in (("task", "task"), ("job", "job_id"), ("attempt", "attempt_id"), ("request_id", "worker_request_id"), ("class", "class")):
        check(f"checkpoint {k} exact", cp.get(k) == planrec[pk])
    check("checkpoint handled_ids == [request id] exactly (no other handled work)", cp.get("handled_ids") == [planrec["worker_request_id"]], handled_ids=cp.get("handled_ids"))
    final_path = bus / "checkpoints" / alias / "final.json"
    final = {}
    with contextlib.suppress(common.BusError):
        final = common.read_json(final_path)
    check("final record present (worker-written; consistency only)", bool(final), path=str(final_path))
    check("final record fields == plan/observed (envelope, request, identity, task, job, attempt)",
          final.get("envelope_sha256") == planrec["envelope_sha256"] and final.get("request_id") == planrec["worker_request_id"]
          and final.get("identity") == identity and final.get("task") == planrec["task"] and final.get("job") == planrec["job_id"] and final.get("attempt") == planrec["attempt_id"])
    check("final record handled_ids == [request id] exactly", final.get("handled_ids") == [planrec["worker_request_id"]], handled_ids=final.get("handled_ids"))
    check("final record envelope_file == plan", final.get("envelope_file") == planrec["envelope_path"])
    check("final record outcome == terminal state", final.get("outcome") == terminal.get("state"))
    check("checkpoint consistent with the final record", bool(final) and cp.get("handled_ids") == final.get("handled_ids") and cp.get("release_results") == final.get("release_results"))
    # requester-observed ordering (journal), digest-bound to the final record validated above
    events_j = read_journal(run_dir)
    final_ev = next((e for e in events_j if e.get("event") == "final-record-observed"), None)
    term_ev = next((e for e in events_j if e.get("event") == "terminal-observed"), None)
    final_now = sha256_file(final_path) if final_path.is_file() else None
    if final_ev is None:
        unverified("ordering: final record snapshot observed before the terminal reply", reason="final record never sighted by the requester before the reply; worker-written timestamps do not count")
    elif final_ev.get("sha256") != final_now:
        check("final record bytes == the requester's first snapshot (write-once; no later replacement)", False, observed=final_ev.get("sha256"), now=final_now)
    else:
        check("final record bytes == the requester's first snapshot (write-once; no later replacement)", True)
        ordered = (term_ev is not None and final_ev.get("terminal_absent_after_snapshot") is True and term_ev.get("id") == tid
                   and term_ev.get("final_record_seen_before") is True and term_ev.get("final_sha256_now") == final_now and final_ev["t"] < term_ev["t"])
        if term_ev is not None and term_ev.get("id") != tid:
            check("ordering: journaled terminal id == the selected terminal reply", False, journaled=term_ev.get("id"), selected=tid)
        elif final_ev.get("terminal_absent_after_snapshot") is True:
            check("ordering: final record snapshot (digest-bound) observed with no terminal record in .messages after the snapshot, before the selected reply was observed", ordered)
        else:
            unverified("ordering: final record snapshot observed before the terminal reply", reason="a terminal record already existed in .messages when the final record was first snapshotted")
    key = planrec.get("lock_key")
    if key:
        lock_dir = bus / "locks" / key
        check("lock directory absent after the job", not lock_dir.exists())
        held = next((e for e in events_j if e.get("event") == "lock-held-observed"), None)
        if held:
            check("ownership: lock OWNER with the worker's alias+identity observed by the requester during the run", held.get("owner", {}).get("alias") == alias and held.get("owner", {}).get("instance_id") == identity, owner=held.get("owner"))
        else:
            unverified("ownership: lock OWNER with the worker's alias+identity observed during the run", reason="never observed by the requester (polling granularity or the worker skipped acquisition); worker-written release_results do not count")
        # per-artifact snapshot predicates (continuous ownership and durability are NOT claimed by this adapter)
        for e in planrec.get("expected_artifacts", []):
            ev = next((x for x in events_j if x.get("event") == "artifact-observed" and x.get("name") == e["name"]), None)
            p = Path(planrec["effect_dir"]) / e["name"]
            now_sha = sha256_file(p) if p.is_file() and not p.is_symlink() else None
            name = f"ownership: artifact {e['name']} snapshot (content == final content == contract) read while the bound worker's OWNER (same token) was present before and after the read"
            if ev is None:
                unverified(name, reason="artifact never sighted by the requester before completion")
            elif ev.get("sha256") != now_sha or ev.get("sha256") != e["sha256"]:
                check(name, False, observed=ev.get("sha256"), now=now_sha, expected=e["sha256"], reason="observed content differs from the final/contract content (placeholder replaced after the snapshot)")
            elif ev.get("held_by_bound_worker") is not True:
                if held and ev.get("owner_before") and (ev["owner_before"].get("alias") != alias or ev["owner_before"].get("instance_id") != identity):
                    check(name, False, owner_before=ev.get("owner_before"), owner_after=ev.get("owner_after"), reason="a different OWNER held the key when the artifact was first seen")
                else:
                    unverified(name, reason="first sighting was not bracketed by the bound worker's OWNER (written after release, or observed late)", owner_before=ev.get("owner_before"), owner_after=ev.get("owner_after"))
            else:
                check(name, True, sha256=now_sha)
        rr = final.get("release_results", {}) if final else cp.get("release_results", {})
        entry = rr.get(key) if isinstance(rr, dict) else None
        check("final record release_results[key] records state released for exactly that key (consistency)",
              isinstance(entry, dict) and entry.get("state") == "released" and entry.get("released") == [key], entry=entry)
        token = Path(planrec["coordination_root"]) / ".worker_tokens" / alias / f"{key}.json"
        tb = {}
        with contextlib.suppress(common.BusError):
            tb = common.read_json(token)
        check("worker token bundle exists outside the bus for this alias/instance/key (consistency)",
              bool(tb) and tb.get("alias") == alias and tb.get("instance_id") == identity and key in (tb.get("keys") or {}), path=str(token))
    if planrec.get("effect_dir"):
        directory = Path(planrec["effect_dir"])
        present = sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []
        expected_names = sorted(e["name"] for e in planrec["expected_artifacts"])
        check("effect directory holds exactly the expected artifacts", present == expected_names, present=present, expected=expected_names)
        for e in planrec["expected_artifacts"]:
            p = directory / e["name"]
            ok = _real_inside(p, directory) and sha256_file(p) == e["sha256"]
            check(f"artifact {e['name']} is a real file inside effect_dir with the expected content", ok, actual_sha256=(sha256_file(p) if p.is_file() else None), expected=e["sha256"])
            check(f"final record artifacts[{e['name']}] == expected (consistency)", (final.get("artifacts") or {}).get(e["name"]) == e["sha256"])
        check("done header effect-sha256 == the declared artifact contract digest", terminal.get("effect-sha256") == planrec["expected_effect_header"], expected=planrec["expected_effect_header"], header=terminal.get("effect-sha256"))
    hb_path = bus / "heartbeat" / alias
    hb = hb_path.read_text(encoding="utf-8").splitlines() if hb_path.exists() else []
    check("worker heartbeat idle at exit", bool(hb) and hb[0].split()[-1] == "idle" and len(hb[0].split()) > 1 and hb[0].split()[1] == identity, heartbeat=hb[:1])
    if args.late_id:
        late_path = bus / "inbox" / alias / f"{args.late_id}.md"
        check("late unrelated message still unhandled in the worker inbox", late_path.exists())
        check("late message absent from the worker checkpoint", args.late_id not in json.dumps(cp))
        received = next((r for r in waitrec.get("receipts", []) if r.get("state") == "received"), None)
        late_stored = bus / ".messages" / f"{args.late_id}.md"
        late = busmod.decode(late_stored.read_bytes()) if late_stored.exists() else {}
        times = [parse_utc((received or {}).get("created-at")), parse_utc(late.get("created-at")), parse_utc(args.go_at), parse_utc(terminal.get("created-at"))]
        check("timing received <= late <= GO <= done (message timestamps)", all(times) and times[0] <= times[1] <= times[2] <= times[3], times=[str(t) for t in times])
    failed = [c["check"] for c in checks if c["status"] == "failed"]
    unver = [c["check"] for c in checks if c["status"] == "unverified"]
    snapshot = _snapshot(run_dir, planrec, tid)
    result = {"job": planrec["job_id"], "attempt": planrec["attempt_id"], "worker_alias": alias, "identity": identity,
              "no_failed_checks": not failed, "failed": failed, "unverified": unver, "checks": checks, "verified_at": utc(), "snapshot": snapshot,
              "frozen_envelope_contract": ("PASS" if not failed and not unver else "PASS-WITH-UNVERIFIED" if not failed else "NOT PASS"),
              "limits": ["cessation verified for the process group only",
                         "ordering/ownership are requester-observed SNAPSHOTS (digest-bound); continuous ownership and fsync durability are not established by polling",
                         "worker-written records are consistency checks, not proof of execution", "artifact semantics = declared names/digests only",
                         "pinned inputs = verified snapshot at plan and verify time"]}
    write_once(run_dir / "RESULT.json", result)
    return {"no_failed_checks": result["no_failed_checks"], "failed": failed, "unverified": unver, "contract": result["frozen_envelope_contract"]}


def _snapshot(run_dir: Path, planrec: dict, tid: str | None) -> dict:
    """Everything replay eligibility depends on, RECOMPUTED from the current bytes (never copied from records)."""
    bus = Path(planrec["bus"])
    alias = planrec["worker_alias"]
    archived = bus / "inbox" / alias / "done" / f"{planrec['worker_request_id']}.md"
    tpath = bus / ".messages" / f"{tid}.md" if tid else None
    ep = Path(planrec["envelope_path"])
    return {"plan_sha256": sha256_file(run_dir / "PLAN.json"), "request_sha256": sha256_file(run_dir / "REQUEST.bytes"),
            "envelope_sha256": (sha256_file(ep) if ep.is_file() and not ep.is_symlink() else None),
            "archived_sha256": (sha256_file(archived) if archived.exists() else None), "terminal_id": tid,
            "terminal_sha256": (sha256_file(tpath) if tpath and tpath.is_file() else None),
            "artifacts": ({p.name: sha256_file(p) for p in Path(planrec["effect_dir"]).iterdir() if p.is_file()} if planrec.get("effect_dir") else {}),
            "worker_inbox": sorted(p.name for p in (bus / "inbox" / alias).glob("*.md"))}


# ----------------------------------------------------------------------------- replay (gated, revalidated)

def replay(args: argparse.Namespace) -> dict:
    """Gated exercise: after a full PASS whose recomputed snapshot still holds, republish the identical validated
    request bytes and prove the archived copy is returned, nothing is re-enqueued and artifacts are unchanged."""
    run_dir = Path(args.run_dir).resolve(strict=True)
    planrec = common.read_json(run_dir / "PLAN.json")
    result = common.read_json(run_dir / "RESULT.json")
    if result.get("frozen_envelope_contract") != "PASS" or result.get("failed") or result.get("unverified"):
        raise DelegateError(f"replay is allowed only after contract PASS (found {result.get('frozen_envelope_contract')!r}); nothing published")
    bus = Path(planrec["bus"])
    alias = planrec["worker_alias"]
    snap = result["snapshot"]
    archived = bus / "inbox" / alias / "done" / f"{planrec['worker_request_id']}.md"
    now = _snapshot(run_dir, planrec, snap.get("terminal_id"))
    state = common.read_json(run_dir / "STATE.json").get("state")
    if snap.get("envelope_sha256") != planrec["envelope_sha256"] or snap.get("request_sha256") != planrec["worker_request_sha256"]:
        raise DelegateError("replay refused: the verified snapshot does not match the plan's envelope/request digests; nothing published")
    if now != snap or state != "ended" or (planrec.get("lock_key") and (bus / "locks" / planrec["lock_key"]).exists()) or not archived.exists():
        raise DelegateError("replay refused: current bytes/state differ from the verified snapshot; nothing published")
    request = _validated_request(run_dir, planrec)  # digest, id and recipient re-checked on the buffer that is published
    returned = busmod.publish(bus, request)
    time.sleep(0.5)
    after = {p.name: sha256_file(p) for p in Path(planrec["effect_dir"]).iterdir() if p.is_file()} if planrec.get("effect_dir") else {}
    ok = returned.resolve() == archived.resolve() and after == snap["artifacts"] and not (bus / "inbox" / alias / f"{planrec['worker_request_id']}.md").exists()
    write_once(run_dir / "REPLAY.json", {"returned": str(returned), "archived": str(archived), "artifacts_before": snap["artifacts"], "artifacts_after": after, "idempotent": ok, "at": utc()})
    return {"idempotent": ok}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--bus", required=True); p.add_argument("--policy", required=True); p.add_argument("--run-dir", required=True)
    p.add_argument("--agent", required=True); p.add_argument("--instance", required=True)
    p.add_argument("--job", required=True); p.add_argument("--attempt", default="1"); p.add_argument("--task", required=True)
    p.add_argument("--worker-class", default="job", choices=["consult", "job"])
    p.add_argument("--target-reason", default="fresh worker selected before dispatch"); p.add_argument("--delegated-from", default=None)
    p.add_argument("--template", required=True); p.add_argument("--request-body", required=True); p.add_argument("--skill-dir", required=True)
    p.add_argument("--allowed-effects", required=True); p.add_argument("--lock-key", default=None); p.add_argument("--effect-dir", default=None)
    p.add_argument("--expect", action="append", help="NAME=line:<text> | NAME=sha256:<hex> artifact contract inside effect_dir")
    p.add_argument("--barrier", default=None); p.add_argument("--deadline-s", default="600"); p.add_argument("--pin", action="append")
    p.set_defaults(func=plan)
    pb = sub.add_parser("publish"); pb.add_argument("--run-dir", required=True); pb.set_defaults(func=publish)
    l = sub.add_parser("launch"); l.add_argument("--run-dir", required=True); l.set_defaults(func=_launch_result_wrapper)
    b = sub.add_parser("bind"); b.add_argument("--run-dir", required=True); b.add_argument("--timeout", default="240"); b.set_defaults(func=bind)
    w = sub.add_parser("wait"); w.add_argument("--run-dir", required=True); w.add_argument("--timeout-s", default="600"); w.set_defaults(func=wait)
    v = sub.add_parser("verify"); v.add_argument("--run-dir", required=True); v.add_argument("--late-id", default=None); v.add_argument("--go-at", default=None); v.set_defaults(func=verify)
    r = sub.add_parser("replay"); r.add_argument("--run-dir", required=True); r.set_defaults(func=replay)
    args = parser.parse_args()
    try:
        result = args.func(args)
    except common.BusError as error:
        print(json.dumps({"error": str(error)}), file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True))
    return exit_status(args.command, result)


def exit_status(command: str, result: dict) -> int:
    """0 only for the documented success of each subcommand; 2 = pending; 3 = PASS-WITH-UNVERIFIED; 1 otherwise."""
    if command in {"plan", "publish"}:
        return 0 if result.get("state") == "published" else 1
    if command == "launch":
        return 0 if result.get("state") == "ok" and result.get("task_outcome") == "unclassified" and not result.get("persistence_errors") else 1
    if command == "bind":
        return 0 if result.get("bound") else 2
    if command == "wait":
        return 0 if result.get("terminal") else 2
    if command == "verify":
        return {"PASS": 0, "PASS-WITH-UNVERIFIED": 3}.get(result.get("contract"), 1)
    if command == "replay":
        return 0 if result.get("idempotent") is True else 1
    return 1


if __name__ == "__main__":
    sys.exit(main())
