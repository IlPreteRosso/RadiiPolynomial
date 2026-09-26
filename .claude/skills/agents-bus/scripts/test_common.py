from pathlib import Path
import os
import tempfile
import unittest
from unittest.mock import patch

import common


class GuardFailureTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.bus = Path(self.tmp.name); (self.bus / "locks").mkdir()

    def test_metadata_failure_does_not_acquire_a_directory(self):
        with patch.object(common, "utc", side_effect=RuntimeError("clock unavailable")):
            with self.assertRaisesRegex(RuntimeError, "clock unavailable"):
                with common.guard(self.bus, "meta", "fixture", "session"):
                    self.fail("critical section must not run")
        self.assertFalse((self.bus / "locks" / "meta").exists())

    def test_guard_does_not_require_path_stat_follow_symlinks_keyword(self):
        # Reproduce the older pathlib signature from the recorded incident;
        # this does not claim support for that interpreter across all helpers.
        def old_stat_signature(path):
            return os.stat(path)
        # Current pathlib.exists forwards the new keyword too; emulate its
        # older implementation so the injected fault concerns the guard only.
        with patch.object(Path, "stat", old_stat_signature), \
                patch.object(Path, "exists", lambda path: os.path.exists(path)):
            with common.guard(self.bus, "meta", "fixture", "session"):
                self.assertTrue((self.bus / "locks" / "meta" / "OWNER").exists())
        self.assertFalse((self.bus / "locks" / "meta").exists())

    def test_unknown_directory_identity_is_not_reclaimed(self):
        with patch.object(common.os, "lstat", side_effect=OSError("identity unavailable")):
            with self.assertRaisesRegex(OSError, "identity unavailable"):
                with common.guard(self.bus, "meta", "fixture", "session"):
                    self.fail("critical section must not run")
        directory = self.bus / "locks" / "meta"
        self.assertTrue(directory.is_dir())
        self.assertEqual(list(directory.iterdir()), [])

    def test_body_interruption_cleans_up_owned_guard(self):
        with self.assertRaises(KeyboardInterrupt):
            with common.guard(self.bus, "meta", "fixture", "session"):
                raise KeyboardInterrupt()
        self.assertFalse((self.bus / "locks" / "meta").exists())

    def test_replaced_directory_is_not_removed_on_exit(self):
        directory = self.bus / "locks" / "meta"
        with common.guard(self.bus, "meta", "fixture", "session"):
            directory.rename(self.bus / "original-guard")
            directory.mkdir()
        self.assertTrue(directory.is_dir())
        self.assertTrue((self.bus / "original-guard" / "OWNER").is_file())

    def test_failed_owner_publication_removes_only_own_new_empty_directory(self):
        with patch.object(common, "write_json", side_effect=OSError("disk full")):
            with self.assertRaises(OSError):
                with common.guard(self.bus, "meta", "fixture", "session"):
                    self.fail("critical section must not run")
        self.assertFalse((self.bus / "locks" / "meta").exists())
        with common.guard(self.bus, "meta", "fixture", "session"):
            self.assertTrue((self.bus / "locks" / "meta" / "OWNER").exists())

    def test_failed_no_replace_never_enters_or_removes_foreign_owner(self):
        original = common.write_json
        foreign = {"alias": "peer", "instance_id": "other", "token_sha256": "f" * 64}
        def collision(path, value, **kwargs):
            original(path, foreign)
            return False
        with patch.object(common, "write_json", collision):
            with self.assertRaisesRegex(common.BusError, "Foreign OWNER"):
                with common.guard(self.bus, "meta", "fixture", "session"):
                    self.fail("critical section must not run")
        self.assertEqual(common.read_json(self.bus / "locks" / "meta" / "OWNER"), foreign)

    def test_internal_owner_holds_digest_not_secret(self):
        with common.guard(self.bus, "participants", "fixture", "session"):
            owner = common.read_json(self.bus / "locks" / "participants" / "OWNER")
            self.assertNotIn("token", owner)
            self.assertEqual(len(owner["token_sha256"]), 64)


if __name__ == "__main__":
    unittest.main()
