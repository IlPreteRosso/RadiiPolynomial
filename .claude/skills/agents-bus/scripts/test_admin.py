import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class AdminIntegrationTest(unittest.TestCase):
    def command(self, root, *args, script=None):
        script = script or Path(__file__).with_name("admin.py")
        result = subprocess.run([sys.executable, str(script), *map(str, args)],
                                text=True, capture_output=True, cwd=root)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_fresh_cli_setup_registration_binding_and_lock_cycle(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            script = Path(__file__).with_name("admin.py")
            def command(*args, okay=True):
                result = subprocess.run([sys.executable, str(script), *map(str, args)],
                                        text=True, capture_output=True, cwd=root)
                if okay:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    return json.loads(result.stdout)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertTrue(result.stderr.strip())
                self.assertNotIn("Traceback", result.stderr)
                return result
            init = command("init", "--root", root, "--agent", "agent-a", "--agent", "agent-b")
            self.assertEqual(command("discover", "--root", root)["path"], init["path"])
            args = ["--root", root, "--agent", "agent-a", "--instance", "session-a"]
            command("hello", *args, "--harness", "fixture", "--primary", "in-turn-wait")
            participant_file = Path(init["path"]) / "participants/agent-a.json"
            participant_before = participant_file.read_bytes()
            command("hello", "--root", root, "--agent", "agent-a", "--harness", "fixture",
                    "--instance", "different", okay=False)
            self.assertEqual(participant_file.read_bytes(), participant_before)
            resource = root / "source"; resource.mkdir()
            command("bind", *args, "--key", "source", "--resource", resource)
            token = root / "capability.json"
            command("lock", "acquire", *args, "--key", "source", "--purpose", "exercise",
                    "--token-file", token)
            self.assertEqual(command("lock", "show", "--root", root)["locks"][0]["key"], "source")
            command("lock", "release", *args, "--key", "source", "--token-file", token)
            self.assertEqual(command("lock", "show", "--root", root)["locks"], [])

    def test_cli_partial_activation_preserves_other_recorded_fields(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            self.command(root, "init", "--root", root)
            args = ["hello", "--root", root, "--agent", "alice",
                    "--instance", "session-a", "--harness", "fixture"]
            self.command(root, *args, "--primary", "verified-monitor", "--keepalive", "bounded-waits")
            refreshed = self.command(root, *args, "--primary", "user-relay")
            self.assertEqual(refreshed["activation"],
                             {"primary": "user-relay", "keepalive": "bounded-waits"})
            refreshed = self.command(root, *args, "--keepalive", "verified-continuation")
            self.assertEqual(refreshed["activation"],
                             {"primary": "user-relay", "keepalive": "verified-continuation"})
            self.assertEqual(self.command(root, *args)["activation"], refreshed["activation"])

    def test_cli_init_detects_copied_package_manifest_and_honors_explicit_hash(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = Path(temp).resolve()
            scripts = fixture / "package" / "scripts"
            scripts.mkdir(parents=True)
            source = Path(__file__).parent
            for name in ("admin.py", "bootstrap.py", "common.py", "locking.py", "participants.py"):
                shutil.copy2(source / name, scripts / name)
            manifest_bytes = b'{"name":"synthetic-package","files":{}}\n'
            (scripts.parent / "MANIFEST.json").write_bytes(manifest_bytes)
            root = fixture / "auto-project"
            root.mkdir()
            created = self.command(root, "init", "--root", root, script=scripts / "admin.py")
            expected = hashlib.sha256(manifest_bytes).hexdigest()
            self.assertEqual(created["package"]["manifest_sha256"], expected)
            stored = json.loads((Path(created["path"]) / "bus.json").read_text())
            self.assertEqual(stored["package"]["manifest_sha256"], expected)
            explicit_root = fixture / "explicit-project"
            explicit_root.mkdir()
            explicit = self.command(explicit_root, "init", "--root", explicit_root,
                                    "--package-manifest-sha256", "a" * 64, script=scripts / "admin.py")
            self.assertEqual(explicit["package"]["manifest_sha256"], "a" * 64)
            self.assertEqual((scripts.parent / "MANIFEST.json").read_bytes(), manifest_bytes)

    def test_hello_help_explains_location_and_refresh_defaults(self):
        result = subprocess.run([sys.executable, str(Path(__file__).with_name("admin.py")),
                                 "hello", "--help"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        help_text = " ".join(result.stdout.split())
        for explanation in ("does not override other discovered buses", "default: current directory",
                            "select this 16-hex bus id", "omission mints a fresh id",
                            "reuse the returned id", "omitted fields are preserved on refresh",
                            "new alias default: user-relay", "new alias default: unknown"):
            with self.subTest(explanation=explanation):
                self.assertIn(explanation, help_text)


if __name__ == "__main__":
    unittest.main()
