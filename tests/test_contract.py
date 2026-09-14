"""Host-side contract regressions. Comparator tests are a separate integration job."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from benchmark_contract import metrics, parse_bound, render, scalar

spec = importlib.util.spec_from_file_location("check_source", ROOT / "scripts/check-source.py")
source_policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source_policy)


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("sigma.txt", "1024\n")
        self.write("hverify.txt", "42\n")
        self.write("bound.txt", "[[256,1,2,0,256]]\n")
        self.write("Scheme.lean", "import LeanSphincs.Benchmark.Target\n")
        self.write("Solution.lean", "import LeanSphincs.Submission.Scheme\n")

    def write(self, name, text):
        (self.root / name).write_text(text)

    def imports(self):
        return subprocess.run(["bash", str(ROOT / "scripts/check-submission-imports.sh"),
                               str(self.root)], capture_output=True, text=True)

    def test_compile_time_io_route_rejected(self):
        for code in ('def value : Nat := eval% (pure 1)',
                     'unsafe def helper : IO Nat := pure 1',
                     'unsafe def helper : IO Nat := do\n  IO.FS.writeFile "/tmp/fixture" "x"\n  pure 1\ndef value : Nat := eval% helper'):
            self.write("Solution.lean", "import LeanSphincs.Submission.Scheme\n" + code)
            self.assertNotEqual(self.imports().returncode, 0)

    def test_no_active_product_pricing(self):
        policy = json.loads((ROOT / "benchmark/source-policy.json").read_text())
        self.assertNotIn("score", policy)
        self.assertIsNone(json.loads((ROOT / "benchmark/scoring.json").read_text())["bandwidth_price"])

    def test_valid(self):
        source_policy.check(self.root)
        self.assertEqual(self.imports().returncode, 0)
        sigma, hverify, terms = metrics(self.root)
        self.assertEqual((sigma, hverify), (1024, 42))
        template = render(sigma, hverify, terms)
        self.assertIn("1024 42 [⟨256, 0, 2, 0, 256⟩]", template)
        self.assertNotIn("import LeanSphincs.Submission", template)

    def test_noncanonical_scalars(self):
        for raw in ["0", "01", "-1", "1.0", "1\n2", "1\x00", " 1", "١", "1\r\n"]:
            with self.subTest(raw=raw):
                self.write("sigma.txt", raw)
                with self.assertRaises(ValueError):
                    scalar(self.root / "sigma.txt")

    def test_invalid_bounds(self):
        for raw in ["[]", "null", "[[true,1,2,0,256]]", "[[1,0,2,0,256]]",
                    "[[2,2,2,0,256]]", "[[0,1,2,0,256]]", "[[1,1,-2,0,256]]",
                    "[[1.0,1,2,0,256]]", "[[1,1,2,0,256],[1,1,2,0,256]]",
                    "[[1,1,2,0,256],[1,1,1,0,128]]", "[[1,1,2,0,99999]]"]:
            with self.subTest(raw=raw):
                self.write("bound.txt", raw)
                with self.assertRaises(ValueError):
                    parse_bound(self.root / "bound.txt")

    def test_deep_json_is_a_source_error(self):
        self.write("bound.txt", "[" * 2000 + "0" + "]" * 2000)
        with self.assertRaises(ValueError):
            parse_bound(self.root / "bound.txt")

    def test_fixed_bound_term_limit(self):
        terms = [[1, 1, exponent, 0, 128] for exponent in range(128)]
        self.write("bound.txt", json.dumps(terms))
        self.assertEqual(len(parse_bound(self.root / "bound.txt")), 128)
        self.write("bound.txt", json.dumps(terms + [[1, 1, 128, 0, 128]]))
        with self.assertRaises(ValueError):
            parse_bound(self.root / "bound.txt")

    def test_entrant_cannot_supply_scoring_profile(self):
        self.write("scoring.json", '{"bandwidth_price": 1}')
        with self.assertRaises(ValueError):
            source_policy.check(self.root)

    def test_transitive_helper_import_rejected(self):
        self.write("Solution.lean", "import LeanSphincs.Submission.Helper\n")
        self.write("Helper.lean", "import LeanSphincs.Baseline.Secret\n")
        self.assertNotEqual(self.imports().returncode, 0)

    def test_generated_challenge_import_rejected(self):
        self.write("Solution.lean", "import LeanSphincs.Benchmark.Challenge\n")
        self.assertNotEqual(self.imports().returncode, 0)

    def test_comment_smuggling_and_execution(self):
        for code in ["import\n Mathlib\n", "import Lean\n",
                     'def bait := "--"\nrun_cmd pure ()\n',
                     "import Mathlib\nmacro \"bad\" : tactic => `(tactic| trivial)\n",
                     "import Mathlib\nexample : True := by native_decide\n"]:
            with self.subTest(code=code):
                self.write("Solution.lean", code)
                self.assertNotEqual(self.imports().returncode, 0)

    def test_nested_comments_are_allowed(self):
        self.write("Solution.lean", "/- outer /- import Bad -/ still comment -/\n"
                   "import LeanSphincs.Submission.Scheme\n")
        self.assertEqual(self.imports().returncode, 0)

    def test_symlinks_and_nested_files(self):
        (self.root / "alias.lean").symlink_to(self.root / "Scheme.lean")
        with self.assertRaises(ValueError):
            source_policy.check(self.root)
        self.assertNotEqual(self.imports().returncode, 0)

    def test_size_limit(self):
        self.write("Huge.lean", " " * (4 * 1024 * 1024 + 1))
        with self.assertRaises(ValueError):
            source_policy.check(self.root)

    def test_score_rejects_metrics_changed_after_rendering(self):
        output = self.root / "Challenge.lean"
        snapshot = self.root / "snapshot.json"
        subprocess.run(["python3", str(ROOT / "scripts/render-benchmark-challenge.py"),
                        str(self.root), str(output), str(snapshot)], check=True)
        command = ["python3", str(ROOT / "scripts/write-score.py"), str(self.root), str(snapshot)]
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('"ranked": false', result.stdout)
        self.assertNotIn("score", json.loads(result.stdout))
        self.assertIn("score_pending", json.loads(result.stdout))
        self.write("hverify.txt", "1\n")
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("changed after rendering", result.stderr)


if __name__ == "__main__":
    unittest.main()
