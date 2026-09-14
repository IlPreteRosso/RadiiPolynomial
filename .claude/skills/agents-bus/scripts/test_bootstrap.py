"""Filesystem tests for bootstrap/discovery; no live bus or installed skills."""
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
import json
import multiprocessing
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from bootstrap import DIRECTORIES, discover, initialize
from common import BusError


PACKAGE = {"name": "agents-bus", "manifest_sha256": "a" * 64}


def initialize_worker(root: str, alias: str, bus: str | None = None, barrier=None) -> dict:
    try:
        import bootstrap
        original = bootstrap.write_json
        def synchronized(path, record, **kwargs):
            if barrier is not None and path.name == "bus.json":
                directory, count = barrier
                directory = Path(directory)
                (directory / str(os.getpid())).touch()
                deadline = time.monotonic() + 10
                while len(list(directory.iterdir())) < count:
                    if time.monotonic() > deadline:
                        raise RuntimeError("Test publication barrier timed out")
                    time.sleep(0.001)
            return original(path, record, **kwargs)
        with patch.object(bootstrap, "write_json", synchronized):
            return initialize(Path(root), [alias], bus_path=Path(bus) if bus else None,
                              package=PACKAGE)
    except BusError as error:
        return {"error": str(error)}


@contextmanager
def cwd(directory):
    original = Path.cwd()
    os.chdir(directory)
    try:
        yield
    finally:
        os.chdir(original)


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="agents-bus-bootstrap-")
        self.addCleanup(self.temp.cleanup)
        self.parent = Path(self.temp.name).resolve()
        self.root = self.parent / "project"
        self.root.mkdir()
        self.env = patch.dict(os.environ, {}, clear=False)
        self.env.start()
        self.addCleanup(self.env.stop)
        os.environ.pop("AGENTS_BUS", None)

    def init(self, root=None, aliases=None, **kwargs):
        return initialize(root or self.root, aliases or ["codex", "claude"],
                          package=PACKAGE, **kwargs)

    def rewrite(self, path, record):
        path.write_text(json.dumps(record))

    def test_initialization_creates_valid_bus_and_preserves_gitignore(self):
        ignore = self.root / ".gitignore"
        ignore.write_text("existing-rule\n")
        result = self.init()
        bus = Path(result["path"])
        self.assertEqual(discover(self.root), bus)
        self.assertEqual(result["ignore_line"], "/tmp/agents_bus/")
        self.assertEqual(ignore.read_text(), "existing-rule\n")
        self.assertEqual(result["package"], PACKAGE)
        self.assertEqual(json.loads((bus / "bindings.json").read_text()), {
            "keys": {"state": {"kind": "board", "resource": str(bus / "STATE.md")}}})
        self.assertIn("installed `agents-bus`", (bus / "PROTOCOL.md").read_text())
        self.assertNotIn(str(self.parent), (bus / "PROTOCOL.md").read_text())

    def test_repeat_and_new_alias_preserve_existing_history(self):
        first = self.init()
        bus = Path(first["path"])
        board = bus / "STATE.md"
        board.write_text("# Human edited board\n\nA pending request stays pending.\n")
        protocol = bus / "PROTOCOL.md"
        protocol.write_text("A modified project protocol.\n")
        board_bytes, protocol_bytes = board.read_bytes(), protocol.read_bytes()
        resource = self.root / "source"
        resource.mkdir()
        bindings = json.loads((bus / "bindings.json").read_text())
        bindings["keys"]["source"] = {"resource": str(resource), "kind": "dir"}
        self.rewrite(bus / "bindings.json", bindings)
        again = self.init(aliases=["new-session"])
        self.assertEqual(first["bus_id"], again["bus_id"])
        self.assertEqual(board.read_bytes(), board_bytes)
        self.assertEqual(protocol.read_bytes(), protocol_bytes)
        self.assertEqual(json.loads((bus / "bindings.json").read_text()), bindings)
        self.assertTrue((bus / "inbox/new-session/done").is_dir())

    def test_concurrent_initializers_adopt_identity_and_keep_all_alias_dirs(self):
        aliases = [f"session-{index}" for index in range(16)]
        context = multiprocessing.get_context("spawn")
        barrier_dir = self.parent / "publication-barrier"
        barrier_dir.mkdir()
        with ProcessPoolExecutor(max_workers=4, mp_context=context) as pool:
            futures = [pool.submit(initialize_worker, str(self.root), alias, None,
                                   (str(barrier_dir), 4)) for alias in aliases]
            results = [future.result() for future in futures]
        self.assertTrue(all("error" not in result for result in results), results)
        self.assertEqual(len({result["bus_id"] for result in results}), 1)
        bus = Path(results[0]["path"])
        for alias in aliases:
            self.assertTrue((bus / "inbox" / alias / "done").is_dir())
        self.assertEqual(discover(self.root), bus)

    def test_concurrent_different_roots_have_only_one_winner(self):
        other = self.parent / "other"
        other.mkdir()
        shared = self.parent / "shared-bus"
        context = multiprocessing.get_context("spawn")
        barrier_dir = self.parent / "publication-barrier"
        barrier_dir.mkdir()
        with ProcessPoolExecutor(max_workers=2, mp_context=context) as pool:
            futures = [pool.submit(initialize_worker, str(root), "agent", str(shared),
                                   (str(barrier_dir), 2)) for root in (self.root, other)]
            results = [future.result() for future in futures]
        self.assertEqual(sum("error" not in result for result in results), 1, results)
        winner = next(result for result in results if "error" not in result)
        self.assertEqual(json.loads((shared / "bus.json").read_text())["coordination_root"],
                         winner["coordination_root"])

    def test_process_exit_after_identity_is_repairable(self):
        script = """
import os, sys
from pathlib import Path
import bootstrap
original = bootstrap.write_json
def interrupted(path, record, **kwargs):
    result = original(path, record, **kwargs)
    if path.name == 'bus.json':
        os._exit(73)
    return result
bootstrap.write_json = interrupted
bootstrap.initialize(Path(sys.argv[1]), ['first'], package={'name':'agents-bus','manifest_sha256':'a'*64})
"""
        env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parent))
        result = subprocess.run([sys.executable, "-c", script, str(self.root)], env=env,
                                cwd=self.parent, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 73, result.stderr)
        bus = self.root / "tmp/agents_bus"
        saved = json.loads((bus / "bus.json").read_text())["bus_id"]
        self.assertFalse((self.root / ".agents_bus").exists())
        repaired = self.init()
        self.assertEqual(repaired["bus_id"], saved)
        self.assertTrue((bus / "STATE.md").is_file())
        self.assertEqual(discover(self.root), bus)

    def test_abandoned_stage_is_ignored_and_missing_board_repaired(self):
        bus = self.root / "tmp/agents_bus"
        (bus / ".staging").mkdir(parents=True)
        staged = bus / ".staging/abandoned.json"
        staged.write_text('{"incomplete":')
        result = self.init()
        self.assertEqual(staged.read_text(), '{"incomplete":')
        (bus / "STATE.md").unlink()
        (self.root / ".agents_bus").unlink()
        repaired = self.init()
        self.assertEqual(result["bus_id"], repaired["bus_id"])
        self.assertTrue((bus / "STATE.md").is_file())

    def test_unidentified_live_control_data_is_refused_without_adoption(self):
        for name in ("inbox", "locks", "heartbeat", "checkpoints", "participants", ".messages"):
            with self.subTest(control=name):
                root = self.parent / f"project-{name}"
                root.mkdir()
                control = root / "tmp/agents_bus" / name
                control.mkdir(parents=True)
                if name == "inbox":
                    live = control / "alice/request.md"
                    live.parent.mkdir()
                else:
                    live = control / "existing"
                live.write_text("existing live protocol data\n")
                with self.assertRaisesRegex(BusError, "Unidentified existing bus data"):
                    self.init(root=root)
                self.assertEqual(live.read_text(), "existing live protocol data\n")
                self.assertFalse((control.parent / "bus.json").exists())
                self.assertFalse((root / ".agents_bus").exists())

    def test_unidentified_ownerless_lock_is_live_foreign_data(self):
        bus = self.root / "tmp/agents_bus"
        ownerless = bus / "locks/owned-key"
        ownerless.mkdir(parents=True)
        with self.assertRaisesRegex(BusError, "Unidentified existing bus data"):
            self.init()
        self.assertTrue(ownerless.is_dir())
        self.assertFalse((bus / "bus.json").exists())

    def test_empty_control_directories_and_orphan_stages_are_tolerated(self):
        bus = self.root / "tmp/agents_bus"
        for name in DIRECTORIES:
            (bus / name).mkdir(parents=True, exist_ok=True)
        staged = bus / ".staging/abandoned.json"
        staged.write_text("staged bytes from an interrupted initialization\n")
        # Actual atomic writers stage beside their target, including root markers.
        adjacent = (bus / ".tmp-orphan-identity", self.root / ".tmp-orphan-marker")
        for artifact in adjacent:
            artifact.write_bytes(b"complete unpublished metadata\n")
        result = self.init()
        self.assertEqual(discover(self.root), Path(result["path"]))
        self.assertEqual(staged.read_text(), "staged bytes from an interrupted initialization\n")
        for artifact in adjacent:
            self.assertEqual(artifact.read_bytes(), b"complete unpublished metadata\n")

    def test_conflicting_marker_refused_before_target_effects(self):
        self.init()
        alternate = self.root / "other-bus"
        with self.assertRaisesRegex(BusError, "different bus"):
            self.init(bus_path=alternate)
        self.assertFalse(alternate.exists())

    def test_incompatible_existing_root_refused_before_marker(self):
        result = self.init()
        other = self.parent / "other"
        other.mkdir()
        with self.assertRaisesRegex(BusError, "different coordination root"):
            self.init(root=other, bus_path=Path(result["path"]))
        self.assertFalse((other / ".agents_bus").exists())

    def test_invalid_identity_and_alias_are_refused(self):
        for alias in ("../escape", "", "two words", "name\n", "a" * 65, 7):
            with self.subTest(alias=alias), self.assertRaises(BusError):
                self.init(aliases=[alias])
        self.assertFalse((self.root / "tmp").exists())
        result = self.init()
        bus = Path(result["path"])
        record = json.loads((bus / "bus.json").read_text())
        for change in ({"bus_id": "bad"}, {"schema_version": 99},
                       {"coordination_root": "relative"}, {"package": []}, {"package": None}):
            self.rewrite(bus / "bus.json", {**record, **change})
            with self.subTest(change=change), self.assertRaises(BusError):
                self.init()

    def test_corrupt_bus_marker_bindings_and_board_fail_closed(self):
        result = self.init()
        bus = Path(result["path"])
        for path, content in ((bus / "bus.json", b"{"),
                              (self.root / ".agents_bus", b"{"),
                              (bus / "bindings.json", b"[]"),
                              (bus / "STATE.md", b"\xff")):
            before = path.read_bytes()
            path.write_bytes(content)
            with self.subTest(path=path), self.assertRaises(BusError):
                self.init()
            self.assertEqual(path.read_bytes(), content)
            path.write_bytes(before)

    def test_control_directory_symlink_is_not_adopted(self):
        result = self.init()
        bus = Path(result["path"])
        (bus / "locks").rmdir()
        external = self.parent / "external"
        external.mkdir()
        (bus / "locks").symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(BusError, "real directory"):
            self.init()
        self.assertEqual(list(external.iterdir()), [])

    def test_preexisting_overlapping_bindings_refuse_initialization(self):
        result = self.init()
        bus = Path(result["path"])
        source = self.root / "source"
        source.mkdir()
        child = source / "module.py"
        child.write_text("original source\n")
        bindings_file = bus / "bindings.json"
        original = json.loads(bindings_file.read_text())
        board_bytes = (bus / "STATE.md").read_bytes()
        for resource in (source, child):
            bindings = {"keys": {**original["keys"],
                "first": {"resource": str(source), "kind": "dir"},
                "second": {"resource": str(resource), "kind": "dir" if resource == source else "file"}}}
            self.rewrite(bindings_file, bindings)
            corrupt_bytes = bindings_file.read_bytes()
            with self.subTest(resource=resource), self.assertRaisesRegex(BusError, "overlap"):
                self.init(aliases=["fresh-session"])
            self.assertEqual(bindings_file.read_bytes(), corrupt_bytes)
            self.assertEqual((bus / "STATE.md").read_bytes(), board_bytes)
            self.assertFalse((bus / "inbox/fresh-session").exists())

    def test_nested_markers_require_join_even_with_explicit_or_environment(self):
        outer = self.init()
        nested = self.root / "nested"
        nested.mkdir()
        inner = self.init(root=nested)
        for hints in ({}, {"explicit": Path(inner["path"])},
                      {"environment": Path(outer["path"])}):
            with self.subTest(hints=hints), self.assertRaisesRegex(BusError, "Ambiguous"):
                discover(nested, **hints)
        self.assertEqual(discover(nested, join=outer["bus_id"]), Path(outer["path"]))
        self.assertEqual(discover(nested, explicit=Path(outer["path"]), join=inner["bus_id"]),
                         Path(inner["path"]))

    def test_symlink_candidates_deduplicate_by_realpath(self):
        result = self.init()
        bus = Path(result["path"])
        alias = self.parent / "bus-alias"
        alias.symlink_to(bus, target_is_directory=True)
        self.assertEqual(discover(self.root, explicit=alias, environment=bus), bus)
        marker = json.loads((self.root / ".agents_bus").read_text())
        marker["bus_path"] = str(alias)
        self.rewrite(self.root / ".agents_bus", marker)
        self.assertEqual(discover(self.root, explicit=bus), bus)

    def test_corrupt_candidate_is_fatal_even_with_join(self):
        result = self.init()
        nested = self.root / "nested"
        nested.mkdir()
        (nested / ".agents_bus").write_text("{")
        with self.assertRaises(BusError):
            discover(nested, explicit=Path(result["path"]), join=result["bus_id"])
        (nested / ".agents_bus").unlink()
        with self.assertRaises(BusError):
            discover(self.root, explicit=self.parent / "missing", join=result["bus_id"])
        self.assertFalse((self.parent / "missing").exists())

    def test_marker_identity_mismatch_is_fatal(self):
        self.init()
        marker = json.loads((self.root / ".agents_bus").read_text())
        marker["bus_id"] = "0" * 16
        self.rewrite(self.root / ".agents_bus", marker)
        with self.assertRaisesRegex(BusError, "disagree"):
            discover(self.root)

    def test_explicit_root_controls_discovery_from_foreign_cwd(self):
        result = self.init()
        foreign = self.parent / "installed-skill"
        foreign.mkdir()
        with cwd(foreign):
            self.assertEqual(discover(self.root), Path(result["path"]))
            with self.assertRaisesRegex(BusError, "No bus"):
                discover()
            self.assertEqual(discover(explicit=Path(result["path"])), Path(result["path"]))

    def test_environment_participates_and_does_not_override_marker(self):
        first = self.init()
        other = self.parent / "other"
        other.mkdir()
        second = self.init(root=other)
        with patch.dict(os.environ, {"AGENTS_BUS": second["path"]}):
            with self.assertRaisesRegex(BusError, "Ambiguous"):
                discover(self.root)
            self.assertEqual(discover(self.root, join=first["bus_id"]), Path(first["path"]))

    def test_empty_and_whitespace_environment_hints_are_absent(self):
        result = self.init()
        for empty in ("", " ", "\t\n  "):
            with self.subTest(value=repr(empty)), patch.dict(os.environ, {"AGENTS_BUS": empty}):
                self.assertEqual(discover(self.root), Path(result["path"]))
                self.assertEqual(discover(self.root, explicit=Path(result["path"])),
                                 Path(result["path"]))

    def test_nonempty_environment_path_preserves_meaningful_spaces(self):
        spaced_bus = self.root / " bus with spaces "
        result = self.init(bus_path=spaced_bus)
        with cwd(self.root), patch.dict(os.environ, {"AGENTS_BUS": " bus with spaces "}):
            self.assertEqual(discover(self.root), Path(result["path"]))

    def test_duplicate_id_at_different_realpaths_is_not_deduplicated(self):
        first = self.init()
        nested = self.root / "nested"
        nested.mkdir()
        second = self.init(root=nested)
        bus = Path(second["path"])
        record = json.loads((bus / "bus.json").read_text())
        record["bus_id"] = first["bus_id"]
        self.rewrite(bus / "bus.json", record)
        marker = json.loads((nested / ".agents_bus").read_text())
        marker["bus_id"] = first["bus_id"]
        self.rewrite(nested / ".agents_bus", marker)
        with self.assertRaisesRegex(BusError, "Ambiguous"):
            discover(nested)
        with self.assertRaisesRegex(BusError, "uniquely"):
            discover(nested, join=first["bus_id"])


if __name__ == "__main__":
    unittest.main()
