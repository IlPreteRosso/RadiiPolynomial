from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import common


class GuardFailureTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.bus = Path(self.tmp.name); (self.bus / "locks").mkdir()

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
