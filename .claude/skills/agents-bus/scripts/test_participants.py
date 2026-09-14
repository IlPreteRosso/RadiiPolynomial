"""Isolated participant tests; no real inboxes, sessions, or lock tokens used."""
from __future__ import annotations

import json
import multiprocessing
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import common
import participants


def make_bus(root: Path) -> Path:
    root = root.resolve()
    bus = root / "tmp" / "agents_bus"
    for name in ("participants", "heartbeat", "locks", "inbox"):
        (bus / name).mkdir(parents=True)
    common.write_json(bus / "bus.json", {
        "schema_version": 2, "bus_id": "0123456789abcdef",
        "coordination_root": str(root.resolve()), "created_at": common.utc(),
        "package": {"name": "test", "manifest_sha256": "0" * 64},
    })
    (bus / "STATE.md").write_text("# Existing board\n\n## Shared\n\nKeep this prose.\n")
    return bus


def concurrent_hello(bus: str, instance: str, barrier, queue) -> None:
    barrier.wait(timeout=10)
    try:
        record = participants.hello(Path(bus), "same-alias", "test", instance=instance)
        queue.put(("ok", record["instance_id"]))
    except common.BusError as error:
        queue.put(("refused", str(error)))


class ParticipantTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="participants-fixture-")
        self.addCleanup(self.tmp.cleanup)
        self.bus = make_bus(Path(self.tmp.name))

    def hello(self, **kwargs):
        return participants.hello(self.bus, "alice", "test", **kwargs)

    def test_new_registration_has_honest_activation_and_no_tokens(self):
        record = self.hello()
        self.assertRegex(record["instance_id"], r"^[0-9a-f]{16}$")
        self.assertEqual(record["generation"], 0)
        self.assertEqual(record["activation"], {"primary": "user-relay", "keepalive": "unknown"})
        self.assertFalse(record["board_update_pending"])
        self.assertFalse(record["heartbeat_update_pending"])
        self.assertTrue((self.bus / "inbox/alice/done").is_dir())
        self.assertIn(record["instance_id"], (self.bus / "heartbeat/alice").read_text())
        heartbeat_lines = (self.bus / "heartbeat/alice").read_text().splitlines()
        self.assertEqual(heartbeat_lines[0].split()[-1], "active")
        self.assertEqual(heartbeat_lines[1], "next: registration complete")
        self.assertIn("## alice", (self.bus / "STATE.md").read_text())
        self.assertNotIn("token", json.dumps(record))
        self.assertEqual(list((self.bus / "locks").iterdir()), [])

    def test_same_instance_refresh_preserves_registration_and_old_board(self):
        with patch.object(common, "utc", return_value="2026-09-13T01:00:00Z"):
            first = self.hello(instance="instance-a")
        old_board = (self.bus / "STATE.md").read_bytes()
        activation = {"primary": "verified-test-monitor", "keepalive": "bounded-waits"}
        with patch.object(common, "utc", return_value="2026-09-13T02:00:00Z"):
            second = self.hello(instance="instance-a", activation=activation)
        self.assertEqual(second["registered_at"], first["registered_at"])
        self.assertNotEqual(second["last_seen"], first["last_seen"])
        self.assertEqual(second["activation"], activation)
        self.assertTrue((self.bus / "STATE.md").read_bytes().startswith(old_board))
        self.assertEqual((self.bus / "STATE.md").read_text().count("## alice"), 1)
        self.assertIn("Refreshed registration", (self.bus / "STATE.md").read_text())

    def test_board_updates_stay_in_exact_alias_section_preserving_other_prose(self):
        board = self.bus / "STATE.md"
        before = (b"# Board\r\n\r\n## alice-other\r\n\r\nAnother alias.\r\n\r\n"
                  b"## alice\r\n\r\nAlice's existing prose.\r\n\r\n"
                  b"### Details\r\n\r\nNested prose stays here.\r\n\r\n")
        after = b"## bob\r\n\r\nBob's prose.\r\n\r\n## Shared\r\n\r\nShared prose.\r\n"
        board.write_bytes(before + after)
        self.hello(instance="instance-a")
        self.hello(instance="instance-a")
        updated = board.read_bytes()
        self.assertTrue(updated.startswith(before))
        self.assertTrue(updated.endswith(after))
        inserted = updated[len(before):-len(after)]
        self.assertIn(b"Registered `alice` as `instance-a`", inserted)
        self.assertIn(b"Refreshed registration for `alice` as `instance-a`", inserted)
        self.assertNotIn(b"Registered of", updated)
        self.assertEqual(updated.count(b"## alice\r\n"), 1)
        self.assertEqual(updated[updated.index(b"## bob\r\n"):], after)

    def test_refresh_without_activation_preserves_recorded_capability(self):
        activation = {"primary": "verified-test-monitor", "keepalive": "bounded-waits",
                      "delegate": {"enabled": False}}
        self.hello(instance="instance-a", activation=activation)
        refreshed = self.hello(instance="instance-a")
        self.assertEqual(refreshed["activation"], activation)
        self.assertEqual(common.read_json(self.bus / "participants/alice.json")["activation"], activation)

    def test_partial_activation_refresh_preserves_unspecified_fields(self):
        activation = {"primary": "verified-test-monitor", "keepalive": "bounded-waits",
                      "delegate": {"enabled": False}}
        self.hello(instance="instance-a", activation=activation)
        changed_primary = self.hello(instance="instance-a", activation={"primary": "user-relay"})
        expected = {**activation, "primary": "user-relay"}
        self.assertEqual(changed_primary["activation"], expected)
        changed_keepalive = self.hello(instance="instance-a", activation={"keepalive": "verified-continuation"})
        expected["keepalive"] = "verified-continuation"
        self.assertEqual(changed_keepalive["activation"], expected)
        self.assertEqual(common.read_json(self.bus / "participants/alice.json")["activation"], expected)

    def test_other_instance_and_harness_cannot_overwrite(self):
        self.hello(instance="instance-a")
        paths = [self.bus / name for name in ("participants/alice.json", "heartbeat/alice", "STATE.md")]
        before = [p.read_bytes() for p in paths]
        with self.assertRaisesRegex(common.BusError, "another instance"):
            self.hello(instance="instance-b")
        with self.assertRaisesRegex(common.BusError, "harness"):
            participants.hello(self.bus, "alice", "other", instance="instance-a")
        self.assertEqual([p.read_bytes() for p in paths], before)

    def test_omitted_instance_never_inherits_shared_identity(self):
        self.hello(instance="existing")
        with self.assertRaisesRegex(common.BusError, "another instance"):
            self.hello()
        second_alias = participants.hello(self.bus, "alice-new", "test")
        self.assertNotEqual(second_alias["instance_id"], "existing")

    def test_reserved_lock_names_are_valid_participant_aliases(self):
        record = participants.hello(self.bus, "meta", "Test harness", instance="instance-meta")
        self.assertEqual(record["alias"], "meta")
        self.assertEqual(record["harness"], "Test harness")
        self.assertTrue((self.bus / "participants/meta.json").exists())

    def test_identifier_validation_precedes_path_use(self):
        for bad in ("../alice", "alice/bob", "", "a\nb", ".hidden"):
            with self.subTest(bad=bad), self.assertRaises(common.BusError):
                participants.hello(self.bus, bad, "test", instance="okay")
            with self.subTest(instance=bad), self.assertRaises(common.BusError):
                self.hello(instance=bad)
        self.assertEqual(list((self.bus / "participants").iterdir()), [])

    def test_ownerless_participants_guard_is_occupied(self):
        occupied = self.bus / "locks/participants"
        occupied.mkdir()
        with self.assertRaisesRegex(common.BusError, "Occupied lock"):
            self.hello(instance="instance-a")
        self.assertTrue(occupied.is_dir())
        self.assertEqual(list((self.bus / "participants").iterdir()), [])

    def test_busy_state_leaves_registration_durable_with_pending_notice(self):
        occupied = self.bus / "locks/state"
        occupied.mkdir()
        board_before = (self.bus / "STATE.md").read_bytes()
        record = self.hello(instance="instance-a")
        self.assertTrue(record["board_update_pending"])
        self.assertIn("Occupied lock: state", record["board_update_error"])
        self.assertEqual(common.read_json(self.bus / "participants/alice.json")["instance_id"], "instance-a")
        self.assertEqual((self.bus / "STATE.md").read_bytes(), board_before)
        self.assertEqual([p.name for p in (self.bus / "locks").iterdir()], ["state"])
        self.assertFalse(record["heartbeat_update_pending"])
        occupied.rmdir()  # Fixture owner releases its own sentinel.
        retried = self.hello(instance="instance-a")
        self.assertFalse(retried["board_update_pending"])
        self.assertEqual((self.bus / "STATE.md").read_text().count("## alice"), 1)

    def test_busy_meta_leaves_board_unchanged_and_reports_pending(self):
        occupied = self.bus / "locks/meta"
        occupied.mkdir()
        before = (self.bus / "STATE.md").read_bytes()
        record = self.hello(instance="instance-a")
        self.assertTrue(record["board_update_pending"])
        self.assertIn("Occupied lock: meta", record["board_update_error"])
        self.assertEqual((self.bus / "STATE.md").read_bytes(), before)
        self.assertTrue(occupied.exists())

    def test_registration_and_heartbeat_write_inside_participant_guard(self):
        original_write_json, original_write_bytes = common.write_json, common.write_bytes
        observed = []

        def checked_json(path, value, **kwargs):
            if path == self.bus / "participants/alice.json":
                self.assertTrue((self.bus / "locks/participants/OWNER").exists())
                observed.append("registration")
            return original_write_json(path, value, **kwargs)

        def checked_bytes(path, value, **kwargs):
            if path == self.bus / "heartbeat/alice":
                self.assertTrue((self.bus / "locks/participants/OWNER").exists())
                observed.append("heartbeat")
            if path == self.bus / "STATE.md":
                self.assertFalse((self.bus / "locks/participants").exists())
                self.assertTrue((self.bus / "locks/meta/OWNER").exists())
                self.assertTrue((self.bus / "locks/state/OWNER").exists())
                observed.append("board")
            return original_write_bytes(path, value, **kwargs)

        with patch.object(common, "write_json", side_effect=checked_json), patch.object(common, "write_bytes", side_effect=checked_bytes):
            self.hello(instance="instance-a")
        self.assertEqual(observed, ["registration", "heartbeat", "board"])

    def test_heartbeat_failure_reports_durable_registration(self):
        (self.bus / "heartbeat/alice").mkdir()
        record = self.hello(instance="instance-a")
        self.assertTrue(record["heartbeat_update_pending"])
        self.assertIn("heartbeat_update_error", record)
        self.assertTrue((self.bus / "participants/alice.json").exists())
        self.assertFalse(record["board_update_pending"])

    def test_corrupt_record_is_not_replaced(self):
        participant_file = self.bus / "participants/alice.json"
        participant_file.write_bytes(b"{broken")
        with self.assertRaisesRegex(common.BusError, "corrupt record"):
            self.hello(instance="instance-a")
        self.assertEqual(participant_file.read_bytes(), b"{broken")

    def test_activation_is_copied_inert_data(self):
        activation = {"delegate": {"enabled": True, "command": "no-command-is-executed"}}
        record = self.hello(instance="instance-a", activation=activation)
        activation["delegate"]["command"] = "mutated"
        self.assertEqual(record["activation"]["delegate"]["command"], "no-command-is-executed")
        with self.assertRaisesRegex(common.BusError, "JSON data"):
            self.hello(instance="instance-a", activation={"primary": lambda: None})

    def test_concurrent_same_alias_has_one_durable_winner(self):
        context = multiprocessing.get_context("spawn")
        barrier, queue = context.Barrier(2), context.Queue()
        processes = [context.Process(target=concurrent_hello,
                                     args=(str(self.bus), f"instance-{number}", barrier, queue))
                     for number in range(2)]
        for process in processes:
            process.start()
        for process in processes:
            process.join(timeout=15)
            if process.is_alive():
                process.terminate()
                process.join()
                self.fail("Concurrent hello did not finish")
            self.assertEqual(process.exitcode, 0)
        results = [queue.get(timeout=2) for _ in processes]
        queue.close()
        self.assertEqual(sorted(kind for kind, _ in results), ["ok", "refused"])
        winner = next(value for kind, value in results if kind == "ok")
        self.assertEqual(common.read_json(self.bus / "participants/same-alias.json")["instance_id"], winner)
        self.assertIn(winner, (self.bus / "heartbeat/same-alias").read_text())
        self.assertEqual(list((self.bus / "locks").iterdir()), [])


if __name__ == "__main__":
    unittest.main()
