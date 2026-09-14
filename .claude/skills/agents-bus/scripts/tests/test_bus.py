"""Isolated behavior tests; never use either agent's real inbox."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tempfile
import threading
import time
import unittest

import bus


class BusTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="test-bus-", dir=Path(__file__).parent)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def message(self, identifier="claude-reply-a", **overrides):
        return {"from": "claude", "to": "codex", "type": "reply", "id": identifier,
                "sender-session": "session-a", "created-at": "2026-09-13T17:20:00Z",
                "re": "codex-request-a", "task": "prototype", "state": "accepted",
                "body": "Complete reply.\n", **overrides}

    def test_staging_and_archive_are_ignored(self):
        inbox = self.root / "inbox/codex"
        (inbox / "done").mkdir(parents=True)
        (inbox / ".tmp-partial.md").write_text("incomplete")
        (inbox / "done/old.md").write_bytes(bus.encode(self.message()))
        self.assertEqual(bus.messages(self.root, "codex"), [])

    def test_retry_is_idempotent_even_after_archive(self):
        message = self.message()
        first = bus.publish(self.root, message)
        inode = first.stat().st_ino
        self.assertEqual(bus.publish(self.root, dict(reversed(list(message.items())))), first)
        self.assertEqual(first.stat().st_ino, inode)
        self.assertEqual(len(list(first.parent.glob("*.md"))), 1)
        archived = first.parent / "done" / first.name
        archived.parent.mkdir()
        first.rename(archived)
        self.assertEqual(bus.publish(self.root, message), archived)
        self.assertFalse(first.exists())

    def test_retry_completes_delivery_after_interrupted_canonical_publication(self):
        message = self.message()
        canonical = self.root / ".messages" / f"{message['id']}.md"
        canonical.parent.mkdir()
        canonical.write_bytes(bus.encode(message))
        delivered = bus.publish(self.root, message)
        self.assertEqual(delivered.read_bytes(), canonical.read_bytes())
        self.assertEqual(delivered.stat().st_ino, canonical.stat().st_ino)
        self.assertEqual(len(bus.messages(self.root, "codex")), 1)

    def test_conflict_cannot_overwrite_or_redirect(self):
        path = bus.publish(self.root, self.message())
        original = path.read_bytes()
        for update in ({"body": "different"}, {"to": "another-agent"}):
            with self.assertRaises(bus.ConflictError):
                bus.publish(self.root, self.message(**update))
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(bus.messages(self.root, "another-agent"), [])

    def test_concurrent_conflicting_writers_have_one_winner(self):
        start = threading.Barrier(2)

        def send(body):
            start.wait()
            try:
                return bus.publish(self.root, self.message(body=body))
            except bus.ConflictError:
                return None

        with ThreadPoolExecutor(max_workers=2) as executor:
            outcomes = list(executor.map(send, ("writer one", "writer two")))
        self.assertEqual(sum(path is not None for path in outcomes), 1)
        delivered = bus.messages(self.root, "codex")
        self.assertEqual(len(delivered), 1)
        self.assertIn(delivered[0]["body"], ("writer one", "writer two"))
        self.assertEqual(list((self.root / ".messages").glob(".tmp-*")), [])

    def test_concurrent_identical_retry_has_one_artifact(self):
        start = threading.Barrier(2)

        def send(_):
            start.wait()
            return bus.publish(self.root, self.message())

        with ThreadPoolExecutor(max_workers=2) as executor:
            outcomes = list(executor.map(send, (1, 2)))
        self.assertEqual(outcomes[0], outcomes[1])
        self.assertEqual(len(bus.messages(self.root, "codex")), 1)

    def test_same_timestamp_different_ids_do_not_collide(self):
        first = bus.publish(self.root, self.message("claude-one"))
        second = bus.publish(self.root, self.message("claude-two"))
        self.assertNotEqual(first, second)
        self.assertEqual(len(bus.messages(self.root, "codex")), 2)

    def test_late_reply_requires_correct_re_and_task(self):
        bus.publish(self.root, self.message("old-unrelated", re="old-request"))
        bus.publish(self.root, self.message("wrong-task", task="other-task"))

        def reply():
            time.sleep(0.04)
            bus.publish(self.root, self.message("new-related"))

        with ThreadPoolExecutor(max_workers=1) as executor:
            sent = executor.submit(reply)
            matches = bus.wait(self.root, "codex", "codex-request-a", 0.6,
                               task="prototype", poll_interval=0.01)
            sent.result()
        self.assertEqual([m["id"] for m in matches], ["new-related"])

    def test_reply_before_waiter_is_received_and_processed_ids_excluded(self):
        bus.publish(self.root, self.message())
        self.assertEqual(len(bus.wait(self.root, "codex", "codex-request-a", 0)), 1)
        self.assertEqual(bus.wait(self.root, "codex", "codex-request-a", 0,
                                  exclude_ids=("claude-reply-a",)), [])

    def test_sender_session_and_version_filters_reject_wrong_queued_messages(self):
        context = {"design-sha256": "a" * 64, "test-run": "unit-run"}
        for identifier, update in (("wrong-sender", {"from": "other-agent"}),
                                   ("wrong-session", {"sender-session": "old-session"}),
                                   ("wrong-version", {"design-sha256": "b" * 64}),
                                   ("wrong-run", {"test-run": "old-run"})):
            bus.publish(self.root, self.message(identifier, **(context | update)))
        options = {"sender": "claude", "sender_session": "session-a", "expected_headers": context}
        self.assertEqual(bus.wait(self.root, "codex", "codex-request-a", 0, **options), [])
        bus.publish(self.root, self.message("early-valid", **context))
        matches = bus.wait(self.root, "codex", "codex-request-a", 0, **options)
        self.assertEqual([message["id"] for message in matches], ["early-valid"])

    def test_filters_accept_late_valid_reply_without_requiring_task(self):
        context = {"design-sha256": "a" * 64}

        def reply():
            time.sleep(0.03)
            message = self.message("late-filtered", **context)
            message.pop("task")
            bus.publish(self.root, message)

        with ThreadPoolExecutor(max_workers=1) as executor:
            sent = executor.submit(reply)
            matches = bus.wait(self.root, "codex", "codex-request-a", 0.6,
                               sender="claude", sender_session="session-a", expected_headers=context,
                               poll_interval=0.01)
            sent.result()
        self.assertEqual([message["id"] for message in matches], ["late-filtered"])

    def test_timeout_is_bounded_and_does_not_touch_locks(self):
        owner = self.root / "locks/resource/OWNER"
        owner.parent.mkdir(parents=True)
        owner.write_text("peer-token remains authoritative")
        before = owner.stat()
        started = time.monotonic()
        self.assertEqual(bus.wait(self.root, "codex", "never-replied", 0.05,
                                  poll_interval=0.01), [])
        elapsed = time.monotonic() - started
        self.assertGreaterEqual(elapsed, 0.04)
        self.assertLess(elapsed, 0.7)
        self.assertEqual(owner.read_text(), "peer-token remains authoritative")
        self.assertEqual(owner.stat().st_mtime_ns, before.st_mtime_ns)
        with self.assertRaises(ValueError):
            bus.wait(self.root, "codex", "never-replied", 56)

    def test_bad_headers_and_traversal_rejected_before_publication(self):
        for updates in ({"id": "../escape"}, {"to": "../peer"},
                        {"sender-session": "line\nfrom: someone"}):
            with self.assertRaises(ValueError):
                bus.publish(self.root, self.message(**updates))
        self.assertEqual(list(self.root.iterdir()), [])

    def test_partial_visible_message_is_error_not_silence(self):
        path = self.root / "inbox/codex/broken.md"
        path.parent.mkdir(parents=True)
        path.write_text("from: claude\n")
        with self.assertRaises(ValueError):
            bus.wait(self.root, "codex", "codex-request-a", 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
