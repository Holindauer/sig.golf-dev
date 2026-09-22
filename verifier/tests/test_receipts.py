"""Early rejection must retain a receipt without attempting compilation."""

import json
from pathlib import Path
import sys
import tempfile
import subprocess
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import verify_submission
from source_bundle import materialize


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_missing_input_never_scores_or_compiles(self):
        with patch.object(verify_submission, "ROOT", self.root), \
             patch.object(verify_submission, "check_dependencies") as dependencies:
            report, directory = verify_submission.verify(self.root / "missing")
        dependencies.assert_not_called()
        self.assertEqual(report["status"], "source_rejected")
        self.assertFalse(report["ranked"])
        self.assertEqual(report["hash_meter"]["id"], "rom256-input64-ceil-v1")
        self.assertNotIn("score", report)
        self.assertEqual(json.loads((directory / "result.json").read_text()), report)

    def test_bad_metric_retains_exact_captured_source(self):
        bundle = {"Scheme.lean": b"", "Solution.lean": b"", "sigma.txt": b"01",
                  "hverify.txt": b"1", "bound.txt": b"[[4,1,1,0,128]]"}
        source = self.root / "input"
        materialize(bundle, source)
        with patch.object(verify_submission, "ROOT", self.root), \
             patch.object(verify_submission, "check_dependencies") as dependencies:
            report, directory = verify_submission.verify(source)
        dependencies.assert_not_called()
        self.assertEqual(report["status"], "source_rejected")
        self.assertNotIn("score", report)
        self.assertEqual((directory / "source/sigma.txt").read_bytes(), b"01")
        self.assertIn("sigma.txt", report["submission"]["files"])

    def test_worker_stdin_is_closed(self):
        log = self.root / "stdin.log"
        code = verify_submission.run([sys.executable, "-c", "import sys; assert sys.stdin.read() == ''"],
                                     self.root, {}, log)
        self.assertEqual(code, 0)

    def test_worker_timeout_is_reported(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            verify_submission.run([sys.executable, "-c", "import time; time.sleep(10)"],
                                  self.root, {}, self.root / "timeout.log", timeout=0.05)


if __name__ == "__main__":
    unittest.main()
