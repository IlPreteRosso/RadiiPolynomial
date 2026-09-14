import json
import hashlib
import os
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

import locking
from common import BusError, write_json


class LocksTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.bus = self.root / "bus"
        for name in ("locks", "participants"):
            (self.bus / name).mkdir(parents=True)
        (self.bus / "STATE.md").write_text("# State\n")
        write_json(self.bus / "bus.json", {"schema_version": 2, "bus_id": "1" * 16,
                                          "coordination_root": str(self.root)})
        write_json(self.bus / "bindings.json", {"keys": {"state": {
            "resource": str(self.bus / "STATE.md"), "kind": "board"}}})
        for alias in ("one", "two"):
            write_json(self.bus / "participants" / f"{alias}.json",
                       {"alias": alias, "instance_id": alias + "-instance"})
        for key in ("a", "ab", "b"):
            (self.root / key).mkdir()
            locking.bind(self.bus, "one", "one-instance", key, self.root / key)

    def acquire(self, keys, name="token", alias="one"):
        return locking.acquire(self.bus, alias, alias + "-instance", keys,
                               purpose="test", token_file=self.root / name)

    def release(self, keys, name="token", alias="one"):
        return locking.release(self.bus, alias, alias + "-instance", keys,
                               token_file=self.root / name)

    def test_multiple_keys_are_owned_and_released(self):
        self.acquire(["b", "a"])
        self.assertEqual({x["key"] for x in locking.show(self.bus)}, {"a", "b"})
        self.release(["a", "b"])
        self.assertEqual(locking.show(self.bus), [])
        repeated = self.release(["a", "b"])
        self.assertEqual(repeated["state"], "not_held")
        self.assertEqual(repeated["released"], [])
        self.assertEqual(repeated["not_held"], ["a", "b"])

    def test_token_file_never_clobbered_and_is_private(self):
        self.acquire(["a"])
        original = (self.root / "token").read_bytes()
        self.assertEqual((self.root / "token").stat().st_mode & 0o777, 0o600)
        with self.assertRaises(BusError):
            self.acquire(["b"])
        self.assertEqual((self.root / "token").read_bytes(), original)
        self.assertFalse((self.bus / "locks" / "b").exists())

    def test_bundle_persisted_before_resource_mkdir(self):
        original = Path.mkdir
        observed = []
        def mkdir(path, *args, **kwargs):
            if path == self.bus / "locks" / "a":
                bundle = json.loads((self.root / "token").read_text())
                self.assertIn("a", bundle["keys"])
                observed.append(True)
            return original(path, *args, **kwargs)
        with patch.object(Path, "mkdir", mkdir):
            self.acquire(["a"])
        self.assertEqual(observed, [True])

    def test_wrong_owner_or_missing_token_cannot_release(self):
        self.acquire(["a"])
        before = (self.bus / "locks" / "a" / "OWNER").read_bytes()
        with self.assertRaises(BusError):
            self.release(["a"], alias="two")
        with self.assertRaises((BusError, FileNotFoundError)):
            self.release(["a"], name="missing")
        self.assertEqual((self.bus / "locks" / "a" / "OWNER").read_bytes(), before)

    def test_old_bundle_never_removes_successor(self):
        self.acquire(["a"])
        self.release(["a"])
        self.acquire(["a"], name="successor")
        before = (self.bus / "locks" / "a" / "OWNER").read_bytes()
        with self.assertRaises(BusError):
            self.release(["a"])
        self.assertEqual((self.bus / "locks" / "a" / "OWNER").read_bytes(), before)

    def test_release_owner_check_serializes_with_acquire_and_duplicate(self):
        self.acquire(["a"])
        reading = threading.Event(); proceed = threading.Event(); errors = []
        original = locking.read_json
        def reader(path):
            value = original(path)
            if path == self.bus / "locks" / "a" / "OWNER":
                reading.set()
                if not proceed.wait(3):
                    raise AssertionError("release test did not resume")
            return value
        def worker():
            try:
                self.release(["a"])
            except Exception as error:
                errors.append(error)
        with patch.object(locking, "read_json", reader):
            thread = threading.Thread(target=worker); thread.start()
            try:
                self.assertTrue(reading.wait(3))
                with self.assertRaises(BusError):
                    self.acquire(["a"], name="successor")
                with self.assertRaises(BusError):
                    self.release(["a"])
            finally:
                proceed.set(); thread.join(3)
        self.assertFalse(thread.is_alive()); self.assertFalse(errors)
        self.acquire(["a"], name="successor")

    def test_ownerless_lock_preserved(self):
        (self.bus / "locks" / "a").mkdir()
        with self.assertRaises(BusError):
            self.acquire(["a"])
        self.assertTrue((self.bus / "locks" / "a").is_dir())
        self.assertFalse((self.bus / "locks" / "a" / "OWNER").exists())

    def test_partial_acquisition_rolls_back_only_own_subset(self):
        self.acquire(["b"], name="peer", alias="two")
        before = (self.bus / "locks" / "b" / "OWNER").read_bytes()
        with self.assertRaises(BusError):
            self.acquire(["a", "b"])
        self.assertFalse((self.bus / "locks" / "a").exists())
        self.assertEqual((self.bus / "locks" / "b" / "OWNER").read_bytes(), before)
        self.assertTrue((self.root / "token").exists())

    def test_bindings_are_exact_frozen_and_control_paths_reserved(self):
        self.assertEqual(locking.bind(self.bus, "one", "one-instance", "a", self.root / "a")["state"],
                         "unchanged")
        for key, resource in (("a", self.root / "b"), ("inner", self.root / "a"),
                              ("meta", self.root / "a"), ("participants", self.root / "a"),
                              ("state", self.root / "a"), ("root", self.root),
                              ("../escape", self.root / "a")):
            with self.subTest(key=key, resource=resource), self.assertRaises(BusError):
                locking.bind(self.bus, "one", "one-instance", key, resource)
        # a and ab are separate component paths, both created in setUp.
        self.acquire(["a", "ab"])

    def test_token_inside_bus_rejected(self):
        with self.assertRaises(BusError):
            locking.acquire(self.bus, "one", "one-instance", ["a"], purpose="test",
                            token_file=self.bus / "token")

    def test_claims_checked_without_trusting_matching_alias(self):
        directory = self.root / ".Codex"; directory.mkdir()
        (directory / "coordination.json").write_text(json.dumps([
            {"agent": "one", "files": ["a"], "since": "2026-01-01"}]))
        with self.assertRaises(BusError):
            self.acquire(["a"])
        self.assertFalse((self.bus / "locks" / "a").exists())

    def test_unknown_claim_format_is_not_ignored(self):
        directory = self.root / ".claude"; directory.mkdir()
        (directory / "coordination.json").write_text('{}')
        with self.assertRaises(BusError):
            self.acquire(["a"])

    def test_preexisting_overlapping_bindings_fail_before_acquisition(self):
        path = self.bus / "bindings.json"
        record = json.loads(path.read_text())
        record["keys"]["b"] = dict(record["keys"]["a"])
        write_json(path, record, replace=True)
        with self.assertRaises(BusError):
            self.acquire(["a"])
        self.assertEqual(locking.show(self.bus), [])
        self.assertFalse((self.root / "token").exists())

    def test_edited_state_binding_fails_before_acquisition(self):
        path = self.bus / "bindings.json"
        record = json.loads(path.read_text())
        record["keys"]["state"]["resource"] = str(self.root / "a")
        write_json(path, record, replace=True)
        with self.assertRaises(BusError):
            self.acquire(["b"])
        self.assertEqual(locking.show(self.bus), [])

    def test_owner_and_show_cannot_supply_a_release_token(self):
        self.acquire(["a"])
        bundle = json.loads((self.root / "token").read_text())
        owner_path = self.bus / "locks" / "a" / "OWNER"
        owner = json.loads(owner_path.read_text())
        self.assertNotIn("token", owner)
        self.assertEqual(owner["token_sha256"], hashlib.sha256(bundle["keys"]["a"].encode()).hexdigest())
        self.assertNotIn(bundle["keys"]["a"], json.dumps(locking.show(self.bus)))
        forged = {"bus_id": bundle["bus_id"], "alias": owner["alias"],
                  "instance_id": owner["instance_id"], "keys": {"a": owner["token_sha256"]}}
        write_json(self.root / "forged", forged)
        before = owner_path.read_bytes()
        with self.assertRaises(BusError):
            self.release(["a"], name="forged")
        self.assertEqual(owner_path.read_bytes(), before)
        self.release(["a"])

    def test_show_redacts_raw_tokens_from_legacy_metadata(self):
        self.acquire(["a"])
        owner_path = self.bus / "locks" / "a" / "OWNER"
        record = json.loads(owner_path.read_text()); record["token"] = "sensitive-legacy-token"
        write_json(owner_path, record, replace=True)
        self.assertNotIn("sensitive-legacy-token", json.dumps(locking.show(self.bus)))

    def test_state_is_a_public_board_edit_resource_then_logs_resume(self):
        self.acquire(["state"])
        board = self.bus / "STATE.md"
        board.write_text(board.read_text() + "\nAn operator edit protected by state.\n")
        resource = self.root / "first"; resource.mkdir()
        result = locking.bind(self.bus, "two", "two-instance", "first", resource)
        self.assertTrue(result["board_update_pending"])
        released = self.release(["state"])
        self.assertEqual(released["released"], ["state"])
        resource = self.root / "second"; resource.mkdir()
        result = locking.bind(self.bus, "two", "two-instance", "second", resource)
        self.assertFalse(result["board_update_pending"])
        self.assertIn("An operator edit protected by state.", board.read_text())
        self.assertIn("bound second", board.read_text())

    def test_non_utf8_board_reports_pending_after_bind_commits(self):
        (self.bus / "STATE.md").write_bytes(b"# State\n\xff")
        resource = self.root / "new"; resource.mkdir()
        result = locking.bind(self.bus, "one", "one-instance", "new", resource)
        self.assertEqual(result["state"], "bound")
        self.assertTrue(result["board_update_pending"])
        self.assertIn("new", json.loads((self.bus / "bindings.json").read_text())["keys"])
        self.assertEqual(locking.show(self.bus), [])

    @unittest.skipUnless(hasattr(os, "mkfifo"), "POSIX special-file fixture")
    def test_special_file_cannot_be_committed_as_a_binding(self):
        resource = self.root / "pipe"; os.mkfifo(resource)
        before = (self.bus / "bindings.json").read_bytes()
        with self.assertRaisesRegex(BusError, "regular file or directory"):
            locking.bind(self.bus, "one", "one-instance", "pipe", resource)
        self.assertEqual((self.bus / "bindings.json").read_bytes(), before)
        self.acquire(["a"])

    def test_missing_bound_resource_has_an_actionable_safe_refusal(self):
        (self.root / "a").rmdir()
        with self.assertRaisesRegex(BusError, "a -> .*restore its path"):
            self.acquire(["b"])
        self.assertEqual(locking.show(self.bus), [])
        (self.root / "a").mkdir()
        self.acquire(["b"])

    def test_release_reports_mixed_held_and_not_held_keys(self):
        self.acquire(["a", "b"])
        self.release(["a"])
        result = self.release(["a", "b"])
        self.assertEqual(result["released"], ["b"])
        self.assertEqual(result["not_held"], ["a"])

    def test_binding_cannot_change_during_acquisition_reservation(self):
        reading = threading.Event(); proceed = threading.Event(); errors = []
        original = locking.validate_bindings
        def validate(path):
            result = original(path)
            reading.set()
            if not proceed.wait(3):
                raise AssertionError("reservation test did not resume")
            return result
        def worker():
            try:
                self.acquire(["a"])
            except Exception as error:
                errors.append(error)
        resource = self.root / "new"; resource.mkdir()
        with patch.object(locking, "validate_bindings", validate):
            thread = threading.Thread(target=worker); thread.start()
            try:
                self.assertTrue(reading.wait(3))
                with self.assertRaisesRegex(BusError, "Occupied lock: meta"):
                    locking.bind(self.bus, "two", "two-instance", "new", resource)
            finally:
                proceed.set(); thread.join(3)
        self.assertFalse(thread.is_alive()); self.assertFalse(errors)
        owner = json.loads((self.bus / "locks" / "a" / "OWNER").read_text())
        self.assertEqual(owner["resource"], str(self.root / "a"))


if __name__ == "__main__":
    unittest.main()
