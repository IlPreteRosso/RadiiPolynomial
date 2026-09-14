"""Private unit fixtures are never approval or adoption evidence."""

from copy import deepcopy
import unittest

import gate


class GateTests(unittest.TestCase):
    def packet(self):
        context = {"design-sha256": "a" * 64, "manifest-sha256": "b" * 64,
                   "test-run": "unit-fixture-only"}
        agreements = []
        receipts = []
        for sender, recipient in (("codex", "claude"), ("claude", "codex")):
            agreements.append({"from": sender, "to": recipient, "id": f"{sender}-agree",
                               "sender-session": f"unit-{sender}", "type": "reply",
                               "state": "accepted", "body": gate.AGREEMENT, **context})
            receipts.append({"from": recipient, "to": sender, "id": f"{recipient}-receipt",
                             "sender-session": f"unit-{recipient}", "type": "reply",
                             "state": "received", "re": f"{sender}-agree", **context})
        return {"design_sha": "a" * 64, "manifest_sha": "b" * 64,
                "test_run": "unit-fixture-only",
                "participants": {"codex": "unit-codex", "claude": "unit-claude"},
                "messages": agreements, "receipts": receipts}

    def test_two_exact_agreements_and_explicit_receipts_pass_without_mutation(self):
        packet = self.packet()
        before = deepcopy(packet)
        result = gate.evaluate(packet)
        self.assertTrue(result["ready"], result)
        self.assertEqual(packet, before)
        self.assertEqual(result["agreement_ids"], {"codex": "codex-agree", "claude": "claude-agree"})

    def test_peer_agreement_can_receipt_first_and_explicit_receipt_completes_exchange(self):
        packet = self.packet()
        packet["messages"][1]["received-agreement"] = "codex-agree"
        packet["receipts"] = [packet["receipts"][1]]
        result = gate.evaluate(packet)
        self.assertTrue(result["ready"], result)
        self.assertEqual(result["receipt_ids"]["codex-agree"], "claude-agree")

    def test_missing_actual_peer_cannot_be_replaced_with_another_role(self):
        packet = self.packet()
        packet["messages"][1].update({"from": "simulated-peer", "sender-session": "unit-other"})
        self.assertFalse(gate.evaluate(packet)["ready"])
        packet["messages"] = packet["messages"][:1]
        self.assertFalse(gate.evaluate(packet)["ready"])

    def test_wrong_design_manifest_run_or_session_never_passes(self):
        for key, value in (("design-sha256", "c" * 64), ("manifest-sha256", "d" * 64),
                           ("test-run", "old-run"), ("sender-session", "other-session"),
                           ("to", "other-recipient"), ("type", "info"), ("state", "received")):
            with self.subTest(key=key):
                packet = self.packet()
                packet["messages"][1][key] = value
                self.assertFalse(gate.evaluate(packet)["ready"])

    def test_quoted_or_fenced_examples_are_not_approval(self):
        for body in (f"> {gate.AGREEMENT}", f"    {gate.AGREEMENT}",
                     f'"{gate.AGREEMENT}"', f"`{gate.AGREEMENT}`",
                     f"```text\n{gate.AGREEMENT}\n```", f"~~~\n{gate.AGREEMENT}\n~~~",
                     f"````\n```\n{gate.AGREEMENT}\n````",
                     gate.AGREEMENT + ".", " " + gate.AGREEMENT):
            with self.subTest(body=body):
                packet = self.packet()
                packet["messages"][1]["body"] = body
                self.assertFalse(gate.evaluate(packet)["ready"])

    def test_bare_sentence_after_explanatory_fence_is_approval(self):
        packet = self.packet()
        packet["messages"][1]["body"] = "```\nexample\n```\n\n" + gate.AGREEMENT + "\n"
        self.assertTrue(gate.evaluate(packet)["ready"])

    def test_receipts_alone_never_establish_agreement(self):
        packet = self.packet()
        packet["messages"] = packet["receipts"]
        for message in packet["messages"]:
            message["body"] = gate.AGREEMENT
        self.assertFalse(gate.evaluate(packet)["ready"])

    def test_each_direction_needs_receipt_and_receipts_of_receipts_do_not_count(self):
        for index in (0, 1):
            packet = self.packet()
            packet["receipts"].pop(index)
            result = gate.evaluate(packet)
            self.assertFalse(result["ready"])
            self.assertTrue(any("receipt" in reason for reason in result["missing"]))
        packet = self.packet()
        packet["receipts"][0]["re"] = packet["receipts"][1]["id"]
        self.assertFalse(gate.evaluate(packet)["ready"])

    def test_receipt_has_to_bind_actual_peer_session_and_version(self):
        for key, value in (("from", "codex"), ("sender-session", "wrong-session"),
                           ("design-sha256", "c" * 64), ("manifest-sha256", "d" * 64),
                           ("test-run", "stale-run"), ("state", "accepted"), ("re", "old-agree")):
            with self.subTest(key=key):
                packet = self.packet()
                packet["receipts"][0][key] = value
                self.assertFalse(gate.evaluate(packet)["ready"])

    def test_conflicting_same_id_fails_but_identical_copy_is_allowed(self):
        packet = self.packet()
        duplicate = deepcopy(packet["messages"][0])
        duplicate["path"] = "/private/unit-fixture-only.md"
        packet["messages"].append(duplicate)
        self.assertTrue(gate.evaluate(packet)["ready"])
        duplicate["body"] = "different bytes"
        result = gate.evaluate(packet)
        self.assertFalse(result["ready"])
        self.assertTrue(any("Conflicting" in reason for reason in result["missing"]))

    def test_historical_wrong_hash_cannot_replace_current_approval(self):
        packet = self.packet()
        historical = deepcopy(packet["messages"][1])
        historical.update({"id": "old-claude-agreement", "design-sha256": "c" * 64})
        packet["messages"].append(historical)
        self.assertTrue(gate.evaluate(packet)["ready"])
        packet["messages"].pop(1)
        self.assertFalse(gate.evaluate(packet)["ready"])

    def test_invalid_expected_inputs_are_reported(self):
        for key, value in (("participants", {"codex": "only-one"}),
                           ("design_sha", "not-a-hash"), ("manifest_sha", ""),
                           ("test_run", ""), ("messages", None)):
            with self.subTest(key=key):
                packet = self.packet()
                packet[key] = value
                result = gate.evaluate(packet)
                self.assertFalse(result["ready"])
                self.assertTrue(result["missing"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
