"""Byte-snapshot, filename and isolation regressions; no Lean installation needed."""

import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from source_bundle import capture, manifest, materialize


class BundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.parent = Path(self.temp.name)
        self.source = self.parent / "source"
        self.bundle = {"Scheme.lean": b"import LeanSphincs.Benchmark.Target\n",
                       "Solution.lean": b"import LeanSphincs.Submission.Scheme\n",
                       "sigma.txt": b"1\n", "hverify.txt": b"1\n", "bound.txt": b"[[4,1,1,0,128]]"}
        materialize(self.bundle, self.source)

    def test_capture_is_independent_of_later_edits(self):
        copied = capture(self.source)
        (self.source / "Scheme.lean").write_text("changed")
        (self.source / "sigma.txt").write_text("9")
        materialize(copied, self.parent / "snapshot")
        self.assertEqual(capture(self.parent / "snapshot"), self.bundle)

    def test_manifest_binds_source_names_content_and_metrics(self):
        original = manifest(self.bundle)
        self.assertEqual(original, manifest(dict(reversed(list(self.bundle.items())))))
        for name in self.bundle:
            modified = self.bundle | {name: self.bundle[name] + b" "}
            self.assertNotEqual(original, manifest(modified))
        self.assertNotEqual(original, manifest(self.bundle | {"Helper.lean": b""}))

    def test_rejects_ambiguous_module_names(self):
        for name in ("Bad.Name.lean", "-option.lean", "Bad Name.lean", "Bad\nName.lean", ".lean", "é.lean"):
            with self.subTest(name=name):
                path = self.source / name
                path.write_bytes(b"")
                try:
                    with self.assertRaises(ValueError):
                        capture(self.source)
                finally:
                    path.unlink()

    def test_rejects_root_and_file_symlinks(self):
        alias = self.parent / "alias"
        alias.symlink_to(self.source)
        with self.assertRaises(OSError):
            capture(alias)
        (self.source / "Helper.lean").symlink_to(self.source / "Scheme.lean")
        with self.assertRaises(OSError):
            capture(self.source)

    def test_fifo_does_not_block_reader(self):
        os.mkfifo(self.source / "Helper.lean")
        with self.assertRaises(ValueError):
            capture(self.source)

    def test_rejects_binary_source(self):
        for data in (b"\xff", b"import Mathlib\x00"):
            (self.source / "Helper.lean").write_bytes(data)
            with self.assertRaises(ValueError):
                capture(self.source)

    def test_refuses_existing_snapshot(self):
        with self.assertRaises(FileExistsError):
            materialize(self.bundle, self.source)


if __name__ == "__main__":
    unittest.main()
