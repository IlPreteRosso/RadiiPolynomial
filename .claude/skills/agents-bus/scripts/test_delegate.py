"""Deterministic tests for delegation adapter v5, driven by a fake harness worker.

No AI model is involved: the adapter policy points at fake_worker.py, which performs the real
envelope lifecycle against a real temporary bus. Negative FAKE_WORKER_MODE values are adversarial
witnesses: each must make the read-only verifier report its own specific check, and the requester's
observation journal is the only ordering/ownership evidence that may count as verified.

v4 vocabulary exercised here: `no_failed_checks` / `frozen_envelope_contract` in RESULT.json, the
three evidence classes (verified / failed / unverified), the write-once final-record snapshot, the
per-artifact ownership snapshot, the separation of process exit (`outcome`) from the worker's task
result (`task_outcome`), and the PASS-only gate on replay.

v5 adds: the finalization ordering (SUPERVISOR -> STATE -> journal -> ledger LAST, so the ledger is
`ended` only when everything before it persisted), the PERSISTENCE_ERRORS.json fallback record, the
frozen envelope FILE as a verified predicate, and a task result read only from the harness's
DESIGNATED final response (validation_failed / inconclusive / unclassified).

    cd .../delegation_v1/scripts && PYTHONDONTWRITEBYTECODE=1 \
      PYTHONPATH=<installed agents-bus scripts> python3 -m unittest -v test_delegate
"""
import sys

sys.dont_write_bytecode = True

import argparse
import contextlib
import io
import json
import os
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
SKILL = Path(os.environ.get("AGENTS_BUS_SKILL")
             or HERE.parents[4] / ".claude" / "skills" / "agents-bus")
for entry in (str(SKILL / "scripts"), str(HERE)):
    if entry not in sys.path:
        sys.path.insert(0, entry)

import bootstrap  # noqa: E402
import bus as busmod  # noqa: E402
import common  # noqa: E402
import locking  # noqa: E402
import participants  # noqa: E402

import delegate  # noqa: E402

FAKE_WORKER = HERE / "fake_worker.py"
TEMPLATE = HERE.parent / "references" / "WORKER_ENVELOPE_TEMPLATE.md"
TASK = "fake worker drill"
HEX32 = r"\A[0-9a-f]{32}\Z"
CODEX_ARGV = ["<EXE>", "exec", "--json", "--sandbox", "workspace-write", "--ask-for-approval", "never",
              "--cd", "<ROOT>", "--run-dir", "<RUN_DIR>", "--bus", "<BUS>",
              "--instance-hint", "<WORKER_INSTANCE>", "<ENVELOPE>"]
CLAUDE_ARGV = ["<EXE>", "-p", "--output-format", "stream-json", "--permission-mode", "dontAsk",
               "--session-id", "<WORKER_INSTANCE>", "<ENVELOPE>"]

# Exact check names (delegate.verify is the authority; these are the ones asserted more than once).
CHECKPOINT_HANDLED = "checkpoint handled_ids == [request id] exactly (no other handled work)"
FINAL_HANDLED = "final record handled_ids == [request id] exactly"
WRITE_ONCE = "final record bytes == the requester's first snapshot (write-once; no later replacement)"
TERMINAL_ID_ORDERING = "ordering: journaled terminal id == the selected terminal reply"
FINALIZATION = "launch finalization resolved (no persistence errors; ledger record ended; run state ended)"
ENVELOPE_FILE = "envelope file present as a regular file with the plan's digest"
TASK_RESULT = "worker task result is neither a validation failure nor inconclusive (designated final response)"
SUPERVISOR_OK = "supervisor outcome ok (process exit)"
CESSATION = "process-group cessation verified (scope: PGID only)"


def ownership(name: str) -> str:
    """The per-artifact ownership-snapshot predicate for one declared artifact."""
    return (f"ownership: artifact {name} snapshot (content == final content == contract) read while "
            "the bound worker's OWNER (same token) was present before and after the read")


def setUpModule():
    if not (SKILL / "SKILL.md").is_file():
        raise unittest.SkipTest(f"installed agents-bus skill not found at {SKILL}")
    os.chmod(FAKE_WORKER, 0o755)  # delegate.py substitutes <EXE> with the policy executable


def ns(**fields) -> argparse.Namespace:
    return argparse.Namespace(**fields)


class Launcher(threading.Thread):
    """delegate.launch blocks until the child group ends; it owns the only STOP/kill authority."""

    def __init__(self, run_dir: Path):
        super().__init__(daemon=False)
        self.run_dir = Path(run_dir)
        self.result = None
        self.error = None

    def run(self):
        try:
            self.result = delegate._launch_result_wrapper(ns(run_dir=str(self.run_dir)))
        except BaseException as error:  # re-raised by join_launcher
            self.error = error


class AdapterTest(unittest.TestCase):
    """One temporary coordination root, bus, requester and bound effect directory per test."""

    maxDiff = None

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.bus = self.root / "tmp" / "agents_bus"
        bootstrap.initialize(self.root, ["claude"], bus_path=self.bus)
        self.instance = "claude-requester-1"
        participants.hello(self.bus, "claude", "claude", instance=self.instance)
        self.effect = self.bind_key("workspace")
        self.request_body = self.root / "REQUEST_BODY.md"
        self.request_body.write_text("Write the declared artifacts, release the lock, reply.\n")
        self.runs = self.root / "runs"
        self.runs.mkdir()
        self.policy_path = self.write_policy()
        self.mode("ok")

    # --- fixture helpers -------------------------------------------------
    def bind_key(self, key):
        directory = self.root / "work" / key
        directory.mkdir(parents=True)
        locking.bind(self.bus, "claude", self.instance, key, directory, kind="dir")
        return directory

    def mode(self, value):
        os.environ["FAKE_WORKER_MODE"] = value
        self.addCleanup(os.environ.pop, "FAKE_WORKER_MODE", None)

    def write_policy(self, name="policy.json", executable=None, harness="codex", argv=None,
                     id_source=None, wall_clock_s=300, max_per_hour=8, max_concurrent=4,
                     classes=("consult", "job")):
        path = self.root / name
        common.write_json(path, {
            "harness": harness, "executable": str(executable or FAKE_WORKER),
            "argv_template": list(argv or (CODEX_ARGV if harness == "codex" else CLAUDE_ARGV)),
            "id_source": id_source or ("codex-json-thread" if harness == "codex"
                                       else "claude-stream-json-session"),
            "wall_clock_s": wall_clock_s, "max_per_hour": max_per_hour,
            "max_concurrent": max_concurrent, "classes": list(classes),
            "runner_argv": ["python3"]}, replace=True)
        return path

    def plan(self, job, run_dir, **overrides):
        args = ns(bus=str(self.bus), policy=str(self.policy_path), run_dir=str(run_dir),
                  agent="claude", instance=self.instance, job=job, attempt="1", task=TASK,
                  worker_class="job", target_reason="fresh bounded worker for one declared artifact",
                  delegated_from=None, template=str(TEMPLATE), request_body=str(self.request_body),
                  skill_dir=str(SKILL), allowed_effects=f"write effect.txt containing {job}",
                  lock_key="workspace", effect_dir=str(self.effect),
                  expect=[f"effect.txt=line:{job}"], barrier=None, deadline_s="120",
                  pin=[str(self.request_body)])
        for name, value in overrides.items():
            setattr(args, name, value)
        return delegate.plan(args)

    def launcher(self, run_dir):
        thread = Launcher(run_dir)
        thread.start()
        self.addCleanup(self.stop_launcher, thread)
        return thread

    def stop_launcher(self, thread):
        if thread.is_alive():
            with contextlib.suppress(OSError):
                (thread.run_dir / "STOP").write_text("cleanup\n")
        thread.join(120)

    def join_launcher(self, thread, timeout=180):
        thread.join(timeout)
        self.assertFalse(thread.is_alive(), "delegate.launch did not return")
        if thread.error is not None:
            raise thread.error
        return thread.result

    def poll(self, predicate, timeout=60.0, what="condition"):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            value = predicate()
            if value:
                return value
            time.sleep(0.05)
        self.fail(f"timed out waiting for {what}")

    def bind(self, run_dir, timeout="60"):
        return delegate.bind(ns(run_dir=str(run_dir), timeout=timeout))

    def wait(self, run_dir, timeout_s="90"):
        return delegate.wait(ns(run_dir=str(run_dir), timeout_s=timeout_s))

    def verify(self, run_dir, late_id=None, go_at=None):
        return delegate.verify(ns(run_dir=str(run_dir), late_id=late_id, go_at=go_at))

    def inject_late(self, alias, job):
        late_id = f"{delegate.compact()}-claude-late-{os.urandom(4).hex()}"
        busmod.publish(self.bus, {
            "from": "claude", "to": alias, "type": "request", "id": late_id,
            "sender-session": self.instance, "created-at": delegate.utc(), "task": TASK,
            "job": f"{job}-UNRELATED", "reply-required": "no",
            "body": "Late unrelated message; a correct bounded worker ignores it.\n"})
        return late_id

    def snapshot(self, alias):
        def names(directory):
            return sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []
        return {"messages": names(self.bus / ".messages"),
                "worker_inbox": names(self.bus / "inbox" / alias),
                "worker_done": names(self.bus / "inbox" / alias / "done"),
                "requester_inbox": names(self.bus / "inbox" / "claude"),
                "effect": names(self.effect)}

    def events(self, run_dir):
        return [e["event"] for e in delegate.read_journal(Path(run_dir))]

    def observed_run(self, job, mode="ok", **overrides):
        """plan -> launch -> bind -> wait -> join, stopping BEFORE verify so the test can intervene."""
        self.mode(mode)
        run = self.runs / job
        planned = self.plan(job, run, **overrides)
        thread = self.launcher(run)
        self.assertTrue(self.bind(run)["bound"])
        self.assertEqual(self.wait(run)["terminal"], "done")
        self.join_launcher(thread)
        return planned, run

    def task_result(self, name, lines, *, last_message_argv=False, last_message=None,
                    job="job-tr", attempt="1", unreadable=False, no_stdout=False):
        """Classify a synthetic run: `lines` become stdout.log, and when the argv names a `-o`
        last-message file that file is the designated final response instead."""
        run = self.runs / f"tr-{name}"
        run.mkdir(parents=True)
        if not no_stdout:
            (run / "stdout.log").write_text("".join(line + "\n" for line in lines), encoding="utf-8")
        argv = ["<EXE>", "exec", "--json", "<ENVELOPE bytes>"]
        if last_message_argv:
            path = run / "last_message.txt"
            argv[3:3] = ["-o", str(path)]
            if last_message is not None:
                path.write_text(last_message, encoding="utf-8")
                if unreadable:
                    path.chmod(0)
                    self.addCleanup(lambda: path.chmod(0o600))
        return delegate._task_result(run, {"effective_argv": argv, "job_id": job, "attempt_id": attempt})

    def check_entry(self, run_dir, name):
        return next(c for c in common.read_json(Path(run_dir) / "RESULT.json")["checks"]
                    if c["check"] == name)

    def doctor_journal(self, run_dir, event, **fields):
        """Rewrite the FIRST journalled `event` in place, in delegate.journal's own line format."""
        path = Path(run_dir) / "OBSERVATIONS.jsonl"
        lines, patched = [], False
        for line in path.read_text(encoding="utf-8").splitlines():
            record = json.loads(line)
            if not patched and record.get("event") == event:
                record.update(fields)
                patched = True
            lines.append(json.dumps(record, sort_keys=True))
        self.assertTrue(patched, f"no {event} entry to doctor")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def cycle(self, mode, job, observe=False, late=False, **overrides):
        """plan -> launch -> bind -> wait -> verify; `observe` keeps the requester watching live."""
        self.mode(mode)
        run = self.runs / job
        barrier = self.root / f"GO-{job}"
        if late:
            overrides["barrier"] = str(barrier)
        planned = self.plan(job, run, **overrides)
        thread = self.launcher(run)
        late_id = go_at = None
        if late or observe:
            self.assertTrue(self.bind(run)["bound"])
        if late:
            self.poll(lambda: "receipt-observed" in self.events(run) or
                      busmod.wait(self.bus, "claude", planned["worker_request_id"], 0.0,
                                  sender=planned["worker_alias"]), what="the received reply")
            late_id = self.inject_late(planned["worker_alias"], job)
            go_at = delegate.utc()
            barrier.write_text("go\n")
        if late or observe:
            waited = self.wait(run)
            launched = self.join_launcher(thread)
        else:
            launched = self.join_launcher(thread)
            self.assertTrue(self.bind(run)["bound"])
            waited = self.wait(run)
        verified = self.verify(run, late_id=late_id, go_at=go_at)
        return planned, run, launched, waited, verified

    def assertNotPass(self, run, verified, failures):
        self.assertFalse(verified["no_failed_checks"])
        self.assertEqual(sorted(verified["failed"]), sorted(failures))
        self.assertEqual(common.read_json(run / "RESULT.json")["frozen_envelope_contract"], "NOT PASS")

    # --- (1) happy path: fully verified, then the gated replay -------------
    def test_happy_path_is_fully_verified_then_replay_is_idempotent(self):
        planned, run, launched, waited, verified = self.cycle("ok", "job-a", observe=True)
        self.assertEqual(planned["state"], "published")
        self.assertEqual((launched["state"], launched["exit_code"]), ("ok", 0))
        self.assertTrue(launched["cessation_verified"])
        self.assertEqual((waited["terminal"], waited["receipts"]), ("done", 1))
        self.assertEqual(verified["failed"], [])
        self.assertEqual(verified["unverified"], [])
        self.assertEqual(verified["contract"], "PASS")
        result = common.read_json(run / "RESULT.json")
        self.assertTrue(result["no_failed_checks"])
        self.assertEqual(result["frozen_envelope_contract"], "PASS")
        self.assertTrue(all(c["status"] == "verified" for c in result["checks"]))

        journal = delegate.read_journal(run)
        kinds = [e["event"] for e in journal]
        for event in ("prepared", "published", "spawned", "bound", "receipt-observed",
                      "lock-held-observed", "artifact-observed", "final-record-observed",
                      "terminal-observed", "ended"):
            self.assertIn(event, kinds)
        artifact = next(e for e in journal if e["event"] == "artifact-observed")
        self.assertIs(artifact["held_by_bound_worker"], True)
        self.assertLess(kinds.index("final-record-observed"), kinds.index("terminal-observed"))
        self.assertIs(next(e for e in journal if e["event"] == "terminal-observed")
                      ["final_record_seen_before"], True)

        alias = planned["worker_alias"]
        self.assertEqual((self.effect / "effect.txt").read_text(), "job-a\n")
        final = common.read_json(self.bus / "checkpoints" / alias / "final.json")
        self.assertEqual(final["artifacts"], {"effect.txt": delegate.sha256_file(self.effect / "effect.txt")})
        self.assertEqual(final["release_results"]["workspace"]["released"], ["workspace"])
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "ended")

        before = self.snapshot(alias)
        self.assertTrue(delegate.replay(ns(run_dir=str(run)))["idempotent"])
        self.assertEqual(self.snapshot(alias), before)

    # --- (2) barrier + late message ---------------------------------------
    def test_barrier_run_ignores_a_late_message_and_verifies_ordering(self):
        planned, run, launched, waited, verified = self.cycle("ok", "job-b", late=True)
        self.assertEqual(launched["state"], "ok")
        self.assertEqual(waited["terminal"], "done")
        self.assertEqual(verified["failed"], [])
        self.assertEqual(len(list((self.bus / "inbox" / planned["worker_alias"]).glob("*.md"))), 1)
        names = [c["check"] for c in common.read_json(run / "RESULT.json")["checks"]]
        self.assertIn("late unrelated message still unhandled in the worker inbox", names)
        self.assertIn("timing received <= late <= GO <= done (message timestamps)", names)

    # --- (3) multi-artifact contract digest --------------------------------
    def test_multi_artifact_contract_is_verified(self):
        _, run, _, _, verified = self.cycle(
            "multi_artifact", "job-c", observe=True,
            expect=["a.txt=line:alpha", "b.txt=line:beta"],
            allowed_effects="write a.txt and b.txt in the bound directory")
        self.assertEqual(verified["failed"], [])
        self.assertEqual(verified["unverified"], [])
        self.assertEqual(sorted(p.name for p in self.effect.iterdir()), ["a.txt", "b.txt"])
        planrec = common.read_json(run / "PLAN.json")
        self.assertEqual(planrec["expected_effect_header"],
                         delegate.artifact_header_digest(planrec["expected_artifacts"]))

    def test_consult_class_runs_without_lock_or_artifact(self):
        _, run, _, _, verified = self.cycle("fast", "job-d", worker_class="consult",
                                            lock_key=None, effect_dir=None, expect=None)
        self.assertEqual(verified["failed"], [])
        checkpoint = common.read_json(run / "RESULT.json")
        self.assertFalse([c for c in checkpoint["checks"] if "artifact" in c["check"]])
        self.assertEqual(locking.show(self.bus), [])

    # --- (4)-(10) adversarial witnesses ------------------------------------
    def test_wrong_digest_fails_the_frozen_envelope_contract(self):
        planned, run, _, _, verified = self.cycle("wrong_digest", "job-e")
        self.assertNotPass(run, verified, [
            "checkpoint envelope_sha256 == plan (worker hashed the envelope FILE)",
            "terminal reply envelope-sha256 header == plan",
            "final record fields == plan/observed (envelope, request, identity, task, job, attempt)"])

    def test_bad_handled_id_fails_the_handled_ids_checks(self):
        _, run, _, _, verified = self.cycle("bad_handled", "job-f")
        self.assertNotPass(run, verified, [CHECKPOINT_HANDLED, FINAL_HANDLED])

    def test_extra_handled_id_fails_both_handled_ids_checks(self):
        """v4 tightening: handled_ids must be EXACTLY the request id, so unrelated claimed work fails."""
        _, run, _, _, verified = self.cycle("extra_handled", "job-f2")
        self.assertNotPass(run, verified, [CHECKPOINT_HANDLED, FINAL_HANDLED])
        final = common.read_json(self.bus / "checkpoints" / self.plan_alias(run) / "final.json")
        self.assertEqual(len(final["handled_ids"]), 2)

    def test_unreleased_claim_fails_the_release_results_check(self):
        _, run, _, _, verified = self.cycle("not_released", "job-g")
        self.assertNotPass(run, verified, [
            "final record release_results[key] records state released for exactly that key (consistency)"])
        self.assertFalse((self.bus / "locks" / "workspace").exists())  # the lock itself is free

    def test_release_result_stored_as_a_string_fails_the_release_results_check(self):
        """Real drill A4: a worker stored the helper's printed JSON string instead of the parsed object."""
        _, run, _, _, verified = self.cycle("string_release", "job-g2")
        self.assertNotPass(run, verified, [
            "final record release_results[key] records state released for exactly that key (consistency)"])
        self.assertFalse((self.bus / "locks" / "workspace").exists())

    def test_extra_artifact_fails_the_artifact_contract(self):
        _, run, _, _, verified = self.cycle("extra_artifact", "job-h")
        self.assertNotPass(run, verified, [
            "effect directory holds exactly the expected artifacts",
            "done header effect-sha256 == the declared artifact contract digest"])
        self.assertEqual(sorted(p.name for p in self.effect.iterdir()), ["effect.txt", "other.txt"])

    def test_symlinked_artifact_fails_the_real_file_check(self):
        _, run, _, _, verified = self.cycle("symlink_artifact", "job-i")
        self.assertNotPass(run, verified, [
            "artifact effect.txt is a real file inside effect_dir with the expected content",
            ownership("effect.txt")])  # a symlink hashes to nothing, so the snapshot never matches
        self.assertTrue((self.effect / "effect.txt").is_symlink())

    def test_wrong_identity_is_refused_at_bind_and_reported_by_verify(self):
        self.mode("wrong_identity")
        run = self.runs / "job-j"
        self.plan("job-j", run)
        self.join_launcher(self.launcher(run))
        bound = self.bind(run, timeout="2")
        self.assertFalse(bound["bound"])
        self.assertNotEqual(bound["hello_instance"], bound["observed_identity"])
        self.assertTrue((run / "BIND.pending.json").exists())
        with self.assertRaises(delegate.DelegateError) as caught:
            self.wait(run, timeout_s="5")
        self.assertIn("identity not bound", str(caught.exception))
        verified = self.verify(run)
        self.assertFalse(verified["no_failed_checks"])
        self.assertIn("identity: hello instance == observed", verified["failed"])
        for name in ("supervisor outcome ok", "request archived by the worker (identical bytes)",
                     "lock directory absent after the job",
                     "effect directory holds exactly the expected artifacts",
                     "pinned operating inputs unchanged since plan (verified snapshot, not a claim "
                     "about execution-time reads)"):
            self.assertNotIn(name, verified["failed"])

    def test_handling_the_late_message_fails_the_late_message_checks(self):
        planned, run, _, _, verified = self.cycle("late_handled", "job-k", late=True)
        self.assertNotPass(run, verified, [
            "late unrelated message still unhandled in the worker inbox",
            "late message absent from the worker checkpoint",
            CHECKPOINT_HANDLED, FINAL_HANDLED])
        self.assertEqual(len(list((self.bus / "inbox" / planned["worker_alias"] / "done").glob("*.md"))), 2)

    def test_pinned_input_tampered_before_launch_fails_validation_with_no_bus_footprint(self):
        """Initial validation failure (template step 1): the worker never becomes a bus participant.

        The harness process still exits cleanly, so process exit (`outcome` ok) and the worker's task
        result (`task_outcome` validation_failed) are reported as the two separate v4 fields.
        """
        self.mode("ok")
        run = self.runs / "job-l0"
        planned = self.plan("job-l0", run)
        alias = planned["worker_alias"]
        self.request_body.write_text("TAMPERED before launch\n")  # a pinned operating input
        launched = self.join_launcher(self.launcher(run))
        self.assertEqual((launched["state"], launched["exit_code"]), ("ok", 0))
        self.assertEqual(launched["task_outcome"], "validation_failed")
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        self.assertIn(delegate.VALIDATION_MARKER, (run / "stdout.log").read_text())
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual((supervisor["outcome"], supervisor["task_outcome"]), ("ok", "validation_failed"))
        self.assertEqual(supervisor["task_result_source"], "raw-last-line")  # the fake harness's raw route
        self.assertEqual(sorted(supervisor["task_result"]), ["attempt", "job", "reason"])
        self.assertEqual((supervisor["task_result"]["job"], supervisor["task_result"]["attempt"]),
                         ("job-l0", "1"))  # the payload correlates with THIS run
        self.assertIn("pinned input changed", supervisor["task_result"]["reason"])
        # no bus bookkeeping of any kind may precede a refusal at VALIDATE
        self.assertFalse((self.bus / "participants" / f"{alias}.json").exists())
        self.assertFalse((self.bus / "checkpoints" / alias).exists())
        self.assertFalse((self.bus / "heartbeat" / alias).exists())
        senders = {busmod.decode(p.read_bytes()).get("from")
                   for p in (self.bus / ".messages").glob("*.md")}
        self.assertNotIn(alias, senders)
        state = self.snapshot(alias)
        self.assertEqual(state["worker_inbox"], [f"{planned['worker_request_id']}.md"])  # still pending
        self.assertEqual((state["worker_done"], state["effect"]), ([], []))
        started = time.monotonic()
        pending = self.bind(run, timeout="60")  # nothing can appear without a new launch
        self.assertLess(time.monotonic() - started, 15)
        self.assertFalse(pending["bound"])
        self.assertIn("run ended", pending["not_launched"])

    def test_tampered_pinned_input_blocks_the_worker(self):
        """Pre-effect mismatch: the same tampering AFTER registration keeps the whole lifecycle."""
        self.mode("ok")
        run = self.runs / "job-l"
        barrier = self.root / "GO-job-l"
        planned = self.plan("job-l", run, barrier=str(barrier))
        alias = planned["worker_alias"]
        thread = self.launcher(run)
        self.poll(lambda: (self.bus / "participants" / f"{alias}.json").exists(),
                  what="the worker's registration")
        self.request_body.write_text("TAMPERED after registration\n")  # a pinned operating input
        barrier.write_text("go\n")
        self.assertTrue(self.bind(run)["bound"])
        self.assertEqual(self.wait(run)["terminal"], "blocked")
        self.join_launcher(thread)
        verified = self.verify(run)
        self.assertIn("terminal reply is done", verified["failed"])
        self.assertIn("pinned operating inputs unchanged since plan (verified snapshot, not a claim "
                      "about execution-time reads)", verified["failed"])
        self.assertEqual(common.read_json(run / "RESULT.json")["frozen_envelope_contract"], "NOT PASS")
        self.assertEqual(sorted(p.name for p in self.effect.iterdir()), [])  # no project effect
        final = common.read_json(self.bus / "checkpoints" / alias / "final.json")
        self.assertEqual(final["outcome"], "blocked")
        self.assertEqual(final["artifacts"], {})

    def plan_alias(self, run_dir):
        return common.read_json(Path(run_dir) / "PLAN.json")["worker_alias"]

    def test_split_identity_keeps_the_binding_pending(self):
        self.mode("split_identity")
        run = self.runs / "job-m"
        self.plan("job-m", run)
        self.join_launcher(self.launcher(run))
        for _ in range(2):  # bind never seals while the output carries two identities
            bound = self.bind(run, timeout="2")
            self.assertFalse(bound["bound"])
            self.assertIsNone(bound["observed_identity"])
            self.assertTrue((run / "BIND.pending.json").exists())
            self.assertFalse((run / "BIND.json").exists())
        pending = common.read_json(run / "BIND.pending.json")
        self.assertEqual(len(set(pending["identity_events"])), 2)
        with self.assertRaises(delegate.DelegateError) as caught:
            self.wait(run, timeout_s="5")
        self.assertIn("identity not bound", str(caught.exception))

    # --- (11) pending observations are resumable ---------------------------
    def test_bind_is_pending_before_launch_and_seals_afterwards(self):
        self.mode("fast")
        run = self.runs / "job-n"
        self.plan("job-n", run)
        early = self.bind(run, timeout="1")
        self.assertFalse(early["bound"])
        self.assertTrue((run / "BIND.pending.json").exists())
        self.assertFalse((run / "BIND.json").exists())
        self.assertIn("bind-pending", self.events(run))
        self.join_launcher(self.launcher(run))
        late = self.bind(run)
        self.assertTrue(late["bound"])
        self.assertTrue((run / "BIND.json").exists())
        self.assertEqual(self.bind(run).get("note"), "already bound")
        self.assertEqual(self.wait(run)["terminal"], "done")
        self.assertEqual(self.wait(run).get("note"), "already sealed")

    # --- (12) publish is an idempotent continuation ------------------------
    def test_publish_is_idempotent_and_state_guarded(self):
        self.mode("fast")
        run = self.runs / "job-o"
        planned = self.plan("job-o", run)
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "published")
        again = delegate.publish(ns(run_dir=str(run)))
        self.assertEqual(again["note"], "already published")
        self.assertEqual(again["worker_request_id"], planned["worker_request_id"])
        self.assertEqual(self.events(run).count("published"), 1)
        self.join_launcher(self.launcher(run))
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.publish(ns(run_dir=str(run)))
        self.assertIn("publish needs state prepared, found 'ended'", str(caught.exception))

    # --- (13) supervisor-owned cancellation --------------------------------
    def test_stop_file_cancels_the_run_and_leaves_the_lock_stranded(self):
        self.mode("hold_lock")
        run = self.runs / "job-p"
        planned = self.plan("job-p", run)
        thread = self.launcher(run)
        bound = self.bind(run)
        self.assertTrue(bound["bound"])
        owner = self.poll(lambda: self.owner_of("workspace", planned["worker_alias"],
                                                bound["observed_identity"]),
                          what="the worker's lock OWNER")
        (run / "STOP").write_text(delegate.utc() + "\n")
        launched = self.join_launcher(thread, timeout=120)
        self.assertEqual(launched["state"], "stopped")
        self.assertTrue(launched["cessation_verified"])
        self.assertEqual(common.read_json(self.bus / "locks" / "workspace" / "OWNER"), owner)
        self.assertEqual(sorted(p.name for p in self.effect.iterdir()), [])
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertTrue(supervisor["stopped_by_request"])
        self.assertEqual(supervisor["stop_result"], "none")
        state = common.read_json(run / "STATE.json")
        self.assertEqual((state["state"], state["outcome"]), ("ended", "stopped"))
        self.assertEqual(common.read_json(self.root / ".adapter" / "launch" / "job-p.1.json")["ledger_state"],
                         "ended")

    def owner_of(self, key, alias, instance):
        path = self.bus / "locks" / key / "OWNER"
        if not path.exists():
            return None
        owner = None
        with contextlib.suppress(common.BusError):
            owner = common.read_json(path)
        if owner and owner.get("alias") == alias and owner.get("instance_id") == instance:
            return owner
        return None

    # --- (14) wall clock ----------------------------------------------------
    def test_policy_wall_clock_bounds_the_run(self):
        self.policy_path = self.write_policy(name="fast.json", wall_clock_s=8)
        self.mode("hold_lock")
        run = self.runs / "job-q"
        planned = self.plan("job-q", run, deadline_s="600")
        self.assertEqual(planned["limit_s"], 8)
        start = time.monotonic()
        launched = self.join_launcher(self.launcher(run), timeout=60)
        self.assertEqual(launched["state"], "timeout")
        self.assertTrue(launched["cessation_verified"])
        self.assertLess(time.monotonic() - start, 30)
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertLessEqual(supervisor["limit_s"], 8)
        self.assertTrue(supervisor["killed_by_supervisor"])
        self.assertTrue((self.bus / "locks" / "workspace").is_dir())  # stranded, untouched

    # --- (15)-(17) capacity ledger ------------------------------------------
    def test_max_concurrent_blocks_a_second_launch_until_the_first_ends(self):
        self.policy_path = self.write_policy(name="one.json", max_concurrent=1)
        other = self.bind_key("workspace-b")
        run_a, run_b = self.runs / "job-r", self.runs / "job-s"
        self.plan("job-r", run_a)
        self.plan("job-s", run_b, lock_key="workspace-b", effect_dir=str(other),
                  expect=["effect.txt=line:job-s"])
        self.mode("hold_lock")
        thread = self.launcher(run_a)
        self.poll(lambda: (self.root / ".adapter" / "launch" / "job-r.1.json").exists(),
                  what="the reserved ledger entry")
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate._launch_result_wrapper(ns(run_dir=str(run_b)))
        self.assertIn("max_concurrent", str(caught.exception))
        self.assertEqual(common.read_json(run_b / "STATE.json")["state"], "published")
        self.assertFalse((run_b / "SUPERVISOR.json").exists())
        (run_a / "STOP").write_text(delegate.utc() + "\n")
        self.assertEqual(self.join_launcher(thread, timeout=120)["state"], "stopped")
        self.mode("fast")
        self.assertEqual(self.join_launcher(self.launcher(run_b))["state"], "ok")
        self.assertEqual((other / "effect.txt").read_text(), "job-s\n")

    def test_unsupported_ledger_records_count_as_live(self):
        self.policy_path = self.write_policy(name="one.json", max_concurrent=1)
        legacy = delegate.ledger_dir(self.root)
        legacy.mkdir(parents=True)
        common.write_json(legacy / "legacy.json", {"job_id": "x", "spawned": "unknown"})
        run = self.runs / "job-t"
        self.plan("job-t", run)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertIn("max_concurrent", str(caught.exception))
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "published")
        # bind must not sit out its timeout on a run whose launch was refused (real drill A3 finding)
        started = time.monotonic()
        pending = self.bind(run, timeout="60")
        self.assertLess(time.monotonic() - started, 15)  # returns once the refusal is older than the launch floor
        self.assertFalse(pending["bound"])
        self.assertIn("launch refused", pending["not_launched"])
        self.assertIn("launch refused", common.read_json(run / "BIND.pending.json")["note"])
        self.assertFalse((run / "BIND.json").exists())
        # reconciling the unsupported record (an explicit decision) restores capacity; bind then waits normally
        (legacy / "legacy.json").rename(legacy / "legacy.reconciled")
        self.mode("fast")
        thread = self.launcher(run)
        self.assertTrue(self.bind(run)["bound"])
        self.assertEqual(self.join_launcher(thread)["state"], "ok")

    def test_max_per_hour_blocks_the_second_launch(self):
        self.policy_path = self.write_policy(name="hourly.json", max_per_hour=1)
        other = self.bind_key("workspace-b")
        run_a, run_b = self.runs / "job-u", self.runs / "job-v"
        self.plan("job-u", run_a)
        self.plan("job-v", run_b, lock_key="workspace-b", effect_dir=str(other),
                  expect=["effect.txt=line:job-v"])
        self.mode("fast")
        self.assertEqual(self.join_launcher(self.launcher(run_a))["state"], "ok")
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate._launch_result_wrapper(ns(run_dir=str(run_b)))
        self.assertIn("max_per_hour", str(caught.exception))
        self.assertEqual(sorted(p.name for p in other.iterdir()), [])

    # --- (18)-(19) launch refusals and bracketed failures -------------------
    def test_missing_executable_records_a_launcher_failure(self):
        self.policy_path = self.write_policy(name="absent.json",
                                             executable=self.root / "no-such-dir" / "harness")
        run = self.runs / "job-w"
        self.plan("job-w", run)
        self.assertEqual(delegate._launch_result_wrapper(ns(run_dir=str(run)))["state"], "launcher-failed")
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual(supervisor["outcome"], "launcher-failed")
        self.assertIs(supervisor["spawned"], False)
        state = common.read_json(run / "STATE.json")
        self.assertEqual((state["state"], state["outcome"]), ("ended", "launcher-failed"))
        ledger = common.read_json(self.root / ".adapter" / "launch" / "job-w.1.json")
        self.assertEqual((ledger["ledger_state"], ledger["outcome"]), ("ended", "launcher-failed"))

    def test_expired_deadline_is_refused_before_spawning(self):
        run = self.runs / "job-x"
        self.plan("job-x", run, deadline_s="6")
        time.sleep(7)
        self.assertEqual(delegate._launch_result_wrapper(ns(run_dir=str(run)))["state"],
                         "deadline-expired-before-launch")
        state = common.read_json(run / "STATE.json")
        self.assertEqual((state["state"], state["outcome"]), ("ended", "deadline-expired-before-launch"))
        self.assertFalse((run / "SUPERVISOR.json").exists())
        self.assertFalse((self.root / ".adapter" / "launch").exists())

    def test_cleanup_failure_is_recorded_as_unknown_and_retains_capacity(self):
        self.mode("hold_lock")
        run = self.runs / "job-y"
        planned = self.plan("job-y", run)
        thread = self.launcher(run)
        bound = self.bind(run)
        self.poll(lambda: self.owner_of("workspace", planned["worker_alias"],
                                        bound["observed_identity"]), what="the worker's lock OWNER")
        with mock.patch.object(delegate, "group_state", side_effect=RuntimeError("pgrep exploded")):
            (run / "STOP").write_text(delegate.utc() + "\n")
            with self.assertRaises(RuntimeError):
                self.join_launcher(thread, timeout=120)
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual(supervisor["outcome"], "cleanup-unknown")
        self.assertIn("cleanup_error", supervisor)
        self.assertIs(supervisor["cessation_verified"], False)
        ledger = common.read_json(self.root / ".adapter" / "launch" / "job-y.1.json")
        self.assertEqual(ledger["ledger_state"], "unknown")  # capacity deliberately retained
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "ended")

    def test_setup_failure_after_the_reservation_still_ends_the_run_and_the_ledger(self):
        """Everything after ledger_reserve is bracketed: a setup error must not strand the reservation."""
        self.mode("fast")
        run = self.runs / "job-y2"
        self.plan("job-y2", run)
        with mock.patch.object(delegate, "annotate",
                               side_effect=delegate.DelegateError("annotate exploded")):
            with self.assertRaises(delegate.DelegateError) as caught:
                delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertIn("annotate exploded", str(caught.exception))
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual(supervisor["outcome"], "setup-failed")
        self.assertIs(supervisor["spawned"], False)
        self.assertIn("annotate exploded", supervisor["supervisor_exception"])
        state = common.read_json(run / "STATE.json")
        self.assertEqual((state["state"], state["outcome"]), ("ended", "setup-failed"))
        ledger = common.read_json(self.root / ".adapter" / "launch" / "job-y2.1.json")
        self.assertEqual((ledger["ledger_state"], ledger["outcome"]), ("ended", "setup-failed"))
        for never_written in ("LAUNCH.json", "stdout.log", "stderr.log"):  # no child was spawned
            self.assertFalse((run / never_written).exists(), never_written)
        self.assertEqual(sorted(p.name for p in self.effect.iterdir()), [])

    def test_persistence_failure_at_the_end_is_reported_and_retains_capacity(self):
        """A storage failure while sealing the run is reported, and the ledger entry is NOT freed."""
        self.mode("fast")
        run = self.runs / "job-y3"
        real = delegate.ledger_update

        def flaky(path, **fields):  # the mid-run `running` update succeeds; the final one fails
            if fields.get("ledger_state") in {"ended", "unknown"}:
                raise OSError("ledger write exploded")
            return real(path, **fields)

        self.plan("job-y3", run)
        with mock.patch.object(delegate, "ledger_update", side_effect=flaky):
            with contextlib.redirect_stderr(io.StringIO()) as warning:
                launched = delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertEqual(launched["state"], "ok")
        self.assertTrue(any("ledger write exploded" in e for e in launched["persistence_errors"]))
        self.assertIn("capacity stays reserved until reconciled", warning.getvalue())
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        self.assertEqual(common.read_json(run / "SUPERVISOR.json")["persistence_errors"],
                         launched["persistence_errors"])
        ledger = common.read_json(self.root / ".adapter" / "launch" / "job-y3.1.json")
        self.assertEqual(ledger["ledger_state"], "running")  # capacity deliberately retained
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "ended")
        self.assertEqual((self.effect / "effect.txt").read_text(), "job-y3\n")

    def test_final_supervisor_write_failure_is_still_reported_to_the_caller(self):
        """When the final SUPERVISOR.json write itself fails, the caller-owned report still carries the error."""
        self.mode("fast")
        run = self.runs / "job-y4"
        real = delegate.replace_json
        calls = {"n": 0}

        def flaky(path, value):  # every SUPERVISOR.json write after the child ended fails
            if Path(path).name == "SUPERVISOR.json" and value.get("direct_child_ended_at"):
                raise OSError("supervisor record write exploded")
            return real(path, value)

        self.plan("job-y4", run)
        with mock.patch.object(delegate, "replace_json", side_effect=flaky):
            with contextlib.redirect_stderr(io.StringIO()):
                launched = delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertTrue(any("supervisor record write exploded" in e for e in launched["persistence_errors"]))
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        stale = common.read_json(run / "SUPERVISOR.json")  # the on-disk record is the pre-exit one
        self.assertNotIn("outcome", stale)
        # the ledger is written LAST, so an earlier failure leaves it `unknown`: capacity stays reserved
        self.assertEqual(common.read_json(self.root / ".adapter" / "launch" / "job-y4.1.json")["ledger_state"],
                         "unknown")
        fallback = common.read_json(run / "PERSISTENCE_ERRORS.json")  # the record the caller can reconcile from
        self.assertEqual(fallback["persistence_errors"], launched["persistence_errors"])

    def test_unresolved_ledger_persistence_blocks_verification_and_replay(self):
        """An unreconciled finalization is a FAILED check: the rest of the run may not be called clean."""
        self.mode("fast")
        run = self.runs / "job-y5"
        real = delegate.ledger_update

        def flaky(path, **fields):  # the mid-run `running` update succeeds; the final one fails
            if fields.get("ledger_state") in {"ended", "unknown"}:
                raise OSError("ledger write exploded")
            return real(path, **fields)

        planned = self.plan("job-y5", run)
        with mock.patch.object(delegate, "ledger_update", side_effect=flaky):
            with contextlib.redirect_stderr(io.StringIO()):
                launched = delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        self.assertTrue(self.bind(run)["bound"])
        self.assertEqual(self.wait(run)["terminal"], "done")
        verified = self.verify(run)
        self.assertNotPass(run, verified, [FINALIZATION])
        entry = self.check_entry(run, FINALIZATION)
        self.assertEqual(entry["ledger_state"], "running")  # a failed ledger write leaves the record as it was
        self.assertTrue(any("ledger write exploded" in e for e in entry["persistence_errors"]))
        alias = planned["worker_alias"]
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)
        self.assertEqual(common.read_json(self.root / ".adapter" / "launch" / "job-y5.1.json")["ledger_state"],
                         "running")

    def test_stale_supervisor_record_blocks_verification_and_replay(self):
        """A final supervisor record that never reached disk leaves the whole process story unverifiable."""
        self.mode("fast")
        run = self.runs / "job-y6"
        real = delegate.replace_json

        def flaky(path, value):  # every SUPERVISOR.json write after the child ended fails
            if Path(path).name == "SUPERVISOR.json" and value.get("direct_child_ended_at"):
                raise OSError("supervisor record write exploded")
            return real(path, value)

        planned = self.plan("job-y6", run)
        with mock.patch.object(delegate, "replace_json", side_effect=flaky):
            with contextlib.redirect_stderr(io.StringIO()):
                launched = delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        self.assertTrue(self.bind(run)["bound"])
        self.assertEqual(self.wait(run)["terminal"], "done")
        verified = self.verify(run)
        self.assertEqual(common.read_json(run / "RESULT.json")["frozen_envelope_contract"], "NOT PASS")
        for consequence in (FINALIZATION, SUPERVISOR_OK, TASK_RESULT, CESSATION):
            self.assertIn(consequence, verified["failed"])  # the stale record records no exit at all
        self.assertEqual(self.check_entry(run, FINALIZATION)["ledger_state"], "unknown")
        alias = planned["worker_alias"]
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)

    # --- (20) policy validation ---------------------------------------------
    def test_policy_validation_rejects_unsafe_or_incomplete_argv(self):
        def codex(*replacements):
            argv = list(CODEX_ARGV)
            for old, new in replacements:
                argv[argv.index(old)] = new
            return argv
        cases = {
            "forbidden mode, alias or bypass": codex(("--cd", "--resume=abc")),
            "forbidden mode, alias or bypass|-r": codex(("--cd", "-r")),
            "forbidden mode, alias or bypass|dangerous": codex(("--cd", "--dangerously-skip-permissions")),
            "unsupported value for --sandbox": codex(("workspace-write", "danger-full-access")),
            "duplicate option --sandbox": CODEX_ARGV[:2] + ["--sandbox", "read-only"] + CODEX_ARGV[2:],
            "must start with <EXE> and end with exactly one <ENVELOPE>": ["<EXE>", "<ENVELOPE>", "exec"],
            "unknown argv placeholder": codex(("--cd", "<SECRET>")),
        }
        for label, argv in cases.items():
            with self.subTest(case=label):
                path = self.write_policy(name=f"bad-{abs(hash(label))}.json", argv=argv)
                with self.assertRaises(delegate.DelegateError) as caught:
                    delegate.load_policy(path)
                self.assertIn(label.split("|")[0], str(caught.exception))
        claude_cases = {
            "unsupported value for --output-format":
                [a if a != "stream-json" else "json" for a in CLAUDE_ARGV],
            "unsupported value for --permission-mode":
                [a if a != "dontAsk" else "bypassPermissions" for a in CLAUDE_ARGV],
            "claude argv_template must use -p/--print": [a for a in CLAUDE_ARGV if a != "-p"],
        }
        for label, argv in claude_cases.items():
            with self.subTest(case=label):
                path = self.write_policy(name=f"claude-{abs(hash(label))}.json", harness="claude", argv=argv)
                with self.assertRaises(delegate.DelegateError) as caught:
                    delegate.load_policy(path)
                self.assertIn(label, str(caught.exception))
        self.assertEqual(delegate.load_policy(self.write_policy(name="good-codex.json"))["harness"], "codex")
        self.assertEqual(delegate.load_policy(
            self.write_policy(name="good-claude.json", harness="claude"))["id_source"],
            "claude-stream-json-session")
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.load_policy(self.write_policy(name="tiny.json", wall_clock_s=4))
        self.assertIn("wall_clock_s must exceed the launch floor", str(caught.exception))

    def test_policy_requires_the_bare_json_flag_exactly_once(self):
        """Codex identity is bound from the thread.started event, so --json must be there, bare, once."""
        cases = {
            "missing": [a for a in CODEX_ARGV if a != "--json"],
            "duplicated": CODEX_ARGV[:2] + ["--json"] + CODEX_ARGV[2:],
            "assigned a value": [a if a != "--json" else "--json=1" for a in CODEX_ARGV],
        }
        for label, argv in cases.items():
            with self.subTest(case=label):
                path = self.write_policy(name=f"json-{label.split()[0]}.json", argv=argv)
                with self.assertRaises(delegate.DelegateError) as caught:
                    delegate.load_policy(path)
                self.assertIn("--json", str(caught.exception))
                self.assertIn("exactly once", str(caught.exception))

    # --- (21) plan refusals --------------------------------------------------
    def test_plan_refuses_unsafe_or_incomplete_dispatches(self):
        cases = [
            ("run_dir must live outside the bus", dict(run_dir=self.bus / "inside")),
            ("lock key must be bound by the maintainer", dict(lock_key="not-bound")),
            ("effect_dir must equal the bound resource", dict(effect_dir=str(self.root / "work"))),
            ("class job needs --lock-key, --effect-dir and at least one --expect", dict(expect=None)),
            ("class consult takes no lock", dict(worker_class="consult")),
            ("artifact names are unique bare file names", dict(expect=["sub/dir.txt=line:x"])),
            ("artifact names are unique bare file names",
             dict(expect=["effect.txt=line:x", "effect.txt=line:y"])),
            ("every artifact needs a condition", dict(expect=["effect.txt"])),
            ("every artifact needs a condition", dict(expect=["effect.txt=sha256:nothex"])),
        ]
        for index, (message, overrides) in enumerate(cases):
            with self.subTest(case=f"{index} {message}"):
                run = overrides.pop("run_dir", self.runs / f"refused-{index}")
                with self.assertRaises(delegate.DelegateError) as caught:
                    self.plan(f"job-z{index}", run, **overrides)
                self.assertIn(message, str(caught.exception))
                self.assertFalse(Path(run).exists())
        self.effect.joinpath("stale.txt").write_text("left over\n")
        with self.assertRaises(delegate.DelegateError) as caught:
            self.plan("job-z9", self.runs / "refused-9")
        self.assertIn("effect_dir must be empty before dispatch", str(caught.exception))

    # --- (22) verify is read-only; replay is gated and revalidated -----------
    def test_verify_is_read_only_and_replay_is_gated(self):
        _, run, _, _, verified = self.cycle("bad_handled", "job-aa")
        alias = self.plan_alias(run)
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:  # RESULT.json is write-once
            self.verify(run)
        self.assertIn("record exists", str(caught.exception))
        self.assertEqual(self.snapshot(alias), before)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertIn("NOT PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)

    def test_replay_refuses_when_the_snapshot_no_longer_holds(self):
        """The PASS gate is not enough: the snapshot is RECOMPUTED from the current bytes."""
        planned, run, _, _, verified = self.cycle("ok", "job-ab", observe=True)
        self.assertEqual(verified["contract"], "PASS")  # the gate is open before the drift
        alias = planned["worker_alias"]
        archived = self.bus / "inbox" / alias / "done" / f"{planned['worker_request_id']}.md"
        archived.unlink()
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay refused", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)

    def test_replay_refuses_request_bytes_that_no_longer_match_the_plan(self):
        """Rewritten REQUEST.bytes drift the recomputed snapshot; the forged id is never published."""
        planned, run, _, _, verified = self.cycle("ok", "job-ab2", observe=True)
        self.assertEqual(verified["contract"], "PASS")
        alias = planned["worker_alias"]
        forged_id = f"{delegate.compact()}-claude-req-forged-{os.urandom(4).hex()}"
        forged = busmod.decode((run / "REQUEST.bytes").read_bytes()) | {"id": forged_id}
        (run / "REQUEST.bytes").write_bytes(busmod.encode(forged))
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay refused", str(caught.exception))
        self.assertIn("nothing published", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)
        self.assertFalse((self.bus / ".messages" / f"{forged_id}.md").exists())
        self.assertFalse((self.bus / "inbox" / alias / f"{forged_id}.md").exists())

    def test_publish_preflight_refuses_tampered_request_bytes_without_publishing(self):
        """publish reads REQUEST.bytes once and refuses unless that buffer IS the prepared request."""
        run = self.runs / "job-ab3"
        with mock.patch.object(delegate, "publish", return_value={"state": "prepared"}):
            planned = self.plan("job-ab3", run)  # prepared on purpose; nothing on the bus yet
        alias, request_id = planned["worker_alias"], common.read_json(run / "PLAN.json")["worker_request_id"]
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "prepared")
        before = self.snapshot(alias)
        self.assertNotIn(f"{request_id}.md", before["messages"])
        tampered = busmod.decode((run / "REQUEST.bytes").read_bytes()) | {"body": "REWRITTEN\n"}
        (run / "REQUEST.bytes").write_bytes(busmod.encode(tampered))
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.publish(ns(run_dir=str(run)))
        self.assertIn("REQUEST.bytes differ from the prepared request digest", str(caught.exception))
        self.assertIn("nothing published", str(caught.exception))
        self.assertEqual(self.snapshot(alias), before)
        self.assertFalse((self.bus / "inbox" / alias / f"{request_id}.md").exists())
        self.assertEqual(common.read_json(run / "STATE.json")["state"], "prepared")

    def test_validated_request_refuses_a_different_digest_id_or_recipient(self):
        """The preflight has three independent conditions; each one alone refuses the buffer."""
        run = self.runs / "job-ab4"
        self.plan("job-ab4", run)
        planrec = common.read_json(run / "PLAN.json")
        original = (run / "REQUEST.bytes").read_bytes()
        request = busmod.decode(original)
        cases = [
            ("body", {"body": "REWRITTEN\n"}, False,
             "REQUEST.bytes differ from the prepared request digest"),
            ("id", {"id": f"{delegate.compact()}-claude-req-other-{os.urandom(4).hex()}"}, True,
             "REQUEST.bytes carry a different id or recipient than the plan"),
            ("recipient", {"to": "codex-worker-deadbeef"}, True,
             "REQUEST.bytes carry a different id or recipient than the plan"),
        ]
        for label, fields, repin, message in cases:
            with self.subTest(case=label):
                data = busmod.encode(request | fields)
                (run / "REQUEST.bytes").write_bytes(data)
                # repin: keep the digest condition satisfied so the id/recipient condition is the one that fires
                record = planrec | ({"worker_request_sha256": delegate.sha256_bytes(data)} if repin else {})
                with self.assertRaises(delegate.DelegateError) as caught:
                    delegate._validated_request(run, record)
                self.assertIn(message, str(caught.exception))
                self.assertIn("nothing published", str(caught.exception))
        (run / "REQUEST.bytes").write_bytes(original)
        self.assertEqual(delegate._validated_request(run, planrec)["id"], planrec["worker_request_id"])

    # --- (23) guarded state transitions --------------------------------------
    def test_relaunching_a_finished_run_is_refused(self):
        self.mode("fast")
        run = self.runs / "job-ac"
        self.plan("job-ac", run)
        self.assertEqual(self.join_launcher(self.launcher(run))["state"], "ok")
        supervisor = common.read_json(run / "SUPERVISOR.json")
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate._launch_result_wrapper(ns(run_dir=str(run)))
        self.assertIn("not in ['published']", str(caught.exception))
        state = common.read_json(run / "STATE.json")
        self.assertEqual((state["state"], state["outcome"]), ("ended", "ok"))
        self.assertEqual(common.read_json(run / "SUPERVISOR.json"), supervisor)
        self.assertEqual([entry["state"] for entry in state["history"]],
                         ["prepared", "published", "starting", "running", "ended"])

    # --- (24) unverified classification ---------------------------------------
    def test_unpaced_worker_may_leave_ownership_unverified(self):
        """No failed check, but nothing was observed live either: PASS-WITH-UNVERIFIED gates replay."""
        planned, run, _, _, verified = self.cycle("fast", "job-ad")
        self.assertEqual(verified["failed"], [])
        self.assertEqual(verified["contract"], "PASS-WITH-UNVERIFIED")
        self.assertIn(ownership("effect.txt"), verified["unverified"])
        result = common.read_json(run / "RESULT.json")
        self.assertEqual(result["no_failed_checks"], True)
        for check in result["checks"]:
            self.assertIn(check["status"], {"verified", "unverified"})
        alias = planned["worker_alias"]
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)

    def test_second_artifact_written_after_the_release_is_unverified_and_blocks_replay(self):
        """Only the artifact seen under the worker's OWNER earns the ownership snapshot."""
        planned, run, _, _, verified = self.cycle(
            "second_artifact_late", "job-ad2", observe=True,
            expect=["a.txt=line:alpha", "b.txt=line:beta"],
            allowed_effects="write a.txt and b.txt in the bound directory")
        self.assertEqual(verified["failed"], [])
        self.assertEqual(verified["contract"], "PASS-WITH-UNVERIFIED")
        self.assertIn(ownership("b.txt"), verified["unverified"])
        self.assertNotIn(ownership("a.txt"), verified["unverified"])
        self.assertEqual(self.check_entry(run, ownership("a.txt"))["status"], "verified")
        alias = planned["worker_alias"]
        before = self.snapshot(alias)
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(alias), before)
        self.assertEqual(len(before["messages"]), len(self.snapshot(alias)["messages"]))

    # --- (25) ordering evidence must not be satisfied after the fact ----------
    def test_final_record_written_after_the_reply_is_not_verified_ordering(self):
        """A worker that replies BEFORE writing final.json must not earn verified ordering."""
        _, run, _, _, verified = self.cycle("reversed_final", "job-ae")
        ordering = next(c for c in common.read_json(run / "RESULT.json")["checks"]
                        if c["check"].startswith("ordering:"))
        self.assertNotEqual(ordering["status"], "verified")

    def test_final_record_replaced_after_the_reply_fails_the_write_once_check(self):
        """The final record snapshot is digest-bound: a later replacement is a failure, not silence."""
        planned, run, _, _, verified = self.cycle("final_swap", "job-af", observe=True)
        self.assertNotPass(run, verified, [WRITE_ONCE])
        observed = next(e for e in delegate.read_journal(run) if e["event"] == "final-record-observed")
        entry = self.check_entry(run, WRITE_ONCE)
        self.assertEqual(entry["observed"], observed["sha256"])
        self.assertEqual(entry["now"], delegate.sha256_file(
            self.bus / "checkpoints" / planned["worker_alias"] / "final.json"))
        self.assertNotEqual(entry["observed"], entry["now"])
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())

    def test_a_journalled_terminal_id_that_differs_from_the_reply_fails_ordering(self):
        """The journal is requester-written, and verify still cross-checks it against the reply it chose."""
        _, run = self.observed_run("job-ag")
        self.doctor_journal(run, "terminal-observed", id="bogus")
        verified = self.verify(run)
        self.assertNotPass(run, verified, [TERMINAL_ID_ORDERING])
        self.assertEqual(self.check_entry(run, TERMINAL_ID_ORDERING)["journaled"], "bogus")

    # --- (26) the per-artifact ownership snapshot -----------------------------
    def test_artifact_replaced_after_the_release_fails_the_ownership_snapshot(self):
        """A placeholder written under the lock and replaced afterwards is content drift, not ownership."""
        _, run, _, _, verified = self.cycle("artifact_swap", "job-ah", observe=True)
        self.assertNotPass(run, verified, [ownership("effect.txt")])
        self.assertIn("observed content differs",
                      self.check_entry(run, ownership("effect.txt"))["reason"])
        self.assertEqual((self.effect / "effect.txt").read_text(), "job-ah\n")  # final content is right

    def test_artifact_written_under_a_foreign_owner_fails_the_ownership_snapshot(self):
        """Right bytes, wrong hand: an intruder held the key when the artifact was first seen."""
        _, run, _, _, verified = self.cycle("foreign_owner", "job-ai", observe=True)
        self.assertNotPass(run, verified, [ownership("effect.txt")])
        entry = self.check_entry(run, ownership("effect.txt"))
        self.assertIn("a different OWNER held the key", entry["reason"])
        self.assertNotEqual(entry["owner_before"]["alias"], self.plan_alias(run))
        self.assertFalse((self.bus / "locks" / "workspace").exists())
        self.assertEqual((self.effect / "effect.txt").read_text(), "job-ai\n")

    # --- (27) the frozen envelope FILE must still be the one the plan froze ----
    def test_envelope_file_changed_before_verification_fails_the_envelope_check(self):
        """The envelope is the contract; a copy that no longer hashes to the plan is not that contract."""
        planned, run = self.observed_run("job-ak")
        envelope = Path(common.read_json(run / "PLAN.json")["envelope_path"])
        with open(envelope, "ab") as stream:
            stream.write(b"\n")  # one appended byte after the worker read it
        verified = self.verify(run)
        self.assertNotPass(run, verified, [ENVELOPE_FILE])
        entry = self.check_entry(run, ENVELOPE_FILE)
        self.assertEqual(entry["expected"], planned["envelope_sha256"])
        self.assertNotEqual(entry["now"], entry["expected"])
        before = self.snapshot(planned["worker_alias"])
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(planned["worker_alias"]), before)

    def test_envelope_file_deleted_before_verification_fails_the_envelope_check(self):
        """An absent envelope is not evidence of anything: the predicate fails rather than going silent."""
        planned, run = self.observed_run("job-al")
        Path(common.read_json(run / "PLAN.json")["envelope_path"]).unlink()
        verified = self.verify(run)
        self.assertNotPass(run, verified, [ENVELOPE_FILE])
        self.assertIsNone(self.check_entry(run, ENVELOPE_FILE)["now"])
        self.assertIsNone(common.read_json(run / "RESULT.json")["snapshot"]["envelope_sha256"])
        before = self.snapshot(planned["worker_alias"])
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("replay is allowed only after contract PASS", str(caught.exception))
        self.assertFalse((run / "REPLAY.json").exists())
        self.assertEqual(self.snapshot(planned["worker_alias"]), before)

    # --- (28) the task result comes ONLY from the designated final response ----
    def test_a_marker_in_commentary_is_not_a_task_result(self):
        """Mentioning the refusal marker mid-run is prose; only the final response classifies the run."""
        _, run, launched, _, verified = self.cycle("marker_commentary", "job-am")
        self.assertEqual(verified["failed"], [])
        self.assertEqual(verified["contract"], "PASS-WITH-UNVERIFIED")  # unpaced mode, as with `fast`
        self.assertEqual(launched["task_outcome"], "unclassified")
        self.assertEqual(delegate.exit_status("launch", launched), 0)
        supervisor = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual(supervisor["task_result_source"], "raw-last-line")
        self.assertNotIn("task_result", supervisor)
        self.assertEqual(self.check_entry(run, TASK_RESULT)["status"], "verified")
        self.assertIn(delegate.VALIDATION_MARKER, (run / "stdout.log").read_text())  # it really was printed

    def test_a_final_marker_for_another_job_is_inconclusive(self):
        """The payload must correlate with THIS run; another job's example proves nothing either way."""
        _, run, launched, _, verified = self.cycle("foreign_failure", "job-an")
        self.assertNotPass(run, verified, [TASK_RESULT])
        self.assertEqual(launched["task_outcome"], "inconclusive")
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        entry = self.check_entry(run, TASK_RESULT)
        self.assertEqual(entry["task_outcome"], "inconclusive")
        self.assertIn("job/attempt do not correlate", entry["task_result"]["why"])

    def test_a_final_marker_without_a_payload_is_inconclusive(self):
        """A marker with no structured payload is unreadable, not a refusal and not a success."""
        _, run, launched, _, verified = self.cycle("malformed_failure", "job-ao")
        self.assertNotPass(run, verified, [TASK_RESULT])
        self.assertEqual(launched["task_outcome"], "inconclusive")
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        self.assertIn("malformed payload", self.check_entry(run, TASK_RESULT)["task_result"]["why"])

    def test_task_result_classifies_only_the_designated_final_response(self):
        marker = delegate.VALIDATION_MARKER
        mine = json.dumps({"job": "job-tr", "attempt": "1", "reason": "pinned input changed"})
        theirs = json.dumps({"job": "another-job", "attempt": "1", "reason": "quoted example"})

        def agent(text, kind="item.completed"):
            return json.dumps({"type": kind, "item": {"type": "agent_message", "text": text}})

        cases = {
            "commentary then an ordinary final line": (
                dict(lines=[f"note: I would print {marker} if validation failed",
                            "final response: job job-tr done"]),
                ("unclassified", "raw-last-line", None)),
            "final marker quoting another job": (
                dict(lines=[f"{marker} {theirs}"]),
                ("inconclusive", "raw-last-line", "job/attempt do not correlate with this run")),
            "final marker with no payload": (
                dict(lines=[f"{marker} (no payload here)"]),
                ("inconclusive", "raw-last-line", "malformed payload")),
            "final marker correlated with this run": (
                dict(lines=[f"{marker} {mine}"]),
                ("validation_failed", "raw-last-line", None)),
            "json stream whose last agent message is ordinary": (
                dict(lines=[agent(f"note: {marker} means a refusal"), agent("done: contract satisfied")]),
                ("unclassified", "json-agent-message", None)),
            "json stream whose last agent message is the marker": (
                dict(lines=[agent("working"), agent(f"{marker} {mine}")]),
                ("validation_failed", "json-agent-message", None)),
            "last-message file wins over stdout": (
                dict(lines=["final response: job job-tr done"], last_message_argv=True,
                     last_message=f"{marker} {mine}"),
                ("validation_failed", "last-message-file", None)),
            "last-message file named but missing": (
                dict(lines=[f"{marker} {mine}"], last_message_argv=True),
                ("inconclusive", "last-message-file-missing", "unavailable or empty")),
            "last-message file present but blank": (
                dict(lines=["final response: job job-tr done"], last_message_argv=True, last_message="  \n"),
                ("inconclusive", "last-message-file", "blank output")),
            "last-message file unreadable": (
                dict(lines=["final response: job job-tr done"], last_message_argv=True, last_message="x", unreadable=True),
                ("inconclusive", "last-message-file-unreadable", "unavailable or empty")),
            "stdout with no final response at all": (
                dict(lines=[]),
                ("inconclusive", "no-final-response", "unavailable or empty")),
            "stdout holding only identity events and blank lines": (
                dict(lines=[json.dumps({"type": "thread.started", "thread_id": "abc"}), "   "]),
                ("inconclusive", "no-final-response", "unavailable or empty")),
            "no stdout file": (
                dict(lines=[], no_stdout=True),
                ("inconclusive", "no-stdout", "unavailable or empty")),
        }
        for label, (kwargs, (outcome, source, why)) in cases.items():
            with self.subTest(case=label):
                result = self.task_result(label.replace(" ", "-"), **kwargs)
                self.assertEqual((result["task_outcome"], result["task_result_source"]), (outcome, source))
                if why is not None:
                    self.assertIn(why, result["task_result"]["why"])
                if outcome == "validation_failed":
                    self.assertEqual(result["task_result"],
                                     {"job": "job-tr", "attempt": "1", "reason": "pinned input changed"})
                if outcome == "unclassified":
                    self.assertNotIn("task_result", result)

    def test_a_worker_with_no_final_response_is_inconclusive_and_blocks_certification(self):
        """A run whose designated final response is missing can never be labelled a success (Codex V5-1)."""
        _, run, launched, _, verified = self.cycle("silent_final", "job-sf")
        self.assertEqual(launched["state"], "ok")
        self.assertEqual(launched["task_outcome"], "inconclusive")
        self.assertEqual(delegate.exit_status("launch", launched), 1)
        sup = common.read_json(run / "SUPERVISOR.json")
        self.assertEqual(sup["task_result_source"], "no-final-response")
        self.assertIn(TASK_RESULT, verified["failed"])
        self.assertNotEqual(verified["contract"], "PASS")
        before = sorted(p.name for p in (self.bus / ".messages").glob("*.md"))
        with self.assertRaises(delegate.DelegateError) as caught:
            delegate.replay(ns(run_dir=str(run)))
        self.assertIn("only after contract PASS", str(caught.exception))
        self.assertEqual(sorted(p.name for p in (self.bus / ".messages").glob("*.md")), before)
        self.assertFalse((run / "REPLAY.json").exists())

    # --- (29) exit status is the adapter's whole command-line contract ---------
    def test_exit_status_reports_the_documented_success_of_each_subcommand(self):
        cases = [
            ("plan", {"state": "published"}, 0),
            ("plan", {"state": "prepared"}, 1),
            ("publish", {"state": "published"}, 0),
            ("publish", {"state": "ended"}, 1),
            ("launch", {"state": "ok", "task_outcome": "unclassified"}, 0),
            ("launch", {"state": "ok", "task_outcome": "inconclusive"}, 1),
            ("launch", {"state": "ok"}, 1),  # an unreported task result is not a success
            ("launch", {"state": "ok", "task_outcome": "validation_failed"}, 1),
            ("launch", {"state": "ok", "task_outcome": "unclassified",
                        "persistence_errors": ["ledger: boom"]}, 1),
            ("launch", {"state": "timeout", "task_outcome": "unclassified"}, 1),
            ("launch", {"state": "launcher-failed"}, 1),
            ("bind", {"bound": True}, 0),
            ("bind", {"bound": False}, 2),
            ("wait", {"terminal": "done"}, 0),
            ("wait", {"terminal": None}, 2),
            ("verify", {"contract": "PASS"}, 0),
            ("verify", {"contract": "PASS-WITH-UNVERIFIED"}, 3),
            ("verify", {"contract": "NOT PASS"}, 1),
            ("replay", {"idempotent": True}, 0),
            ("replay", {"idempotent": False}, 1),
            ("unknown-subcommand", {}, 1),
        ]
        for command, result, expected in cases:
            with self.subTest(case=f"{command} {sorted(result.items())}"):
                self.assertEqual(delegate.exit_status(command, result), expected)


if __name__ == "__main__":
    unittest.main()
