"""Structural raw-query caps: Lean constants, nontrivial ranges and profile binding."""

import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent
CLAIM = ROOT / "formal/LeanSphincs/Benchmark/Claim.lean"
PROFILE = VERIFIER / "resources.json"
LEAN_KEYS = {"rawKeygenCap": "raw_keygen_queries", "rawSignCap": "raw_sign_queries",
             "rawVerifyCap": "raw_verify_queries", "sampleKeygenCap": "raw_keygen_samples",
             "sampleSignCap": "raw_sign_samples"}


def lean_caps():
    text = CLAIM.read_text(encoding="utf-8")
    caps = {}
    for name in LEAN_KEYS:
        match = re.search(rf"^def {name} : Nat := 2 \^ (\d+)$", text, re.M)
        assert match, f"{name} must be a power of two pinned in Claim.lean"
        caps[name] = 2 ** int(match.group(1))
    return caps


class RawCapTests(unittest.TestCase):
    def test_claim_has_structural_cap_fields(self):
        text = CLAIM.read_text(encoding="utf-8")
        for field in ("keygen_queries : HasKeygenQueryBound S rawKeygenCap",
                      "sign_queries : HasSignQueryBound S rawSignCap",
                      "verify_raw_queries : HasVerifyQueryBound S rawVerifyCap"):
            self.assertIn(field, text)

    def test_honest_work_inside_nontrivial_ranges(self):
        caps = lean_caps()
        k, s, v = caps["rawKeygenCap"], caps["rawSignCap"], caps["rawVerifyCap"]
        self.assertLess(k + 2**20 * (s + 1) + v, 2**124)
        self.assertLess(k + 2**32 * (s + 1) + v, 2**100)

    def test_resource_profile_matches_lean_when_set(self):
        if not PROFILE.exists():
            self.skipTest("organizer resource profile not present")
        profile = json.loads(PROFILE.read_text(encoding="utf-8"))
        caps = lean_caps()
        for lean_name, key in LEAN_KEYS.items():
            value = profile.get(key)
            if value is not None:
                self.assertEqual(value, caps[lean_name], key)

    def test_statement_caps_match_eligibility_mirror(self):
        spec = importlib.util.spec_from_file_location("eligibility", VERIFIER / "eligibility.py")
        module = importlib.util.module_from_spec(spec)
        sys.path.insert(0, str(VERIFIER))
        spec.loader.exec_module(module)
        caps = lean_caps()
        expected = {key: caps[name] for name, key in LEAN_KEYS.items()}
        self.assertEqual(module.STATEMENT_RAW_CAPS, expected)

    def test_init_attribute_rejected_by_source_policy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "sigma.txt").write_text("1\n")
            (root / "hverify.txt").write_text("1\n")
            (root / "bound.txt").write_text("[[1,1,1,0,128]]\n")
            (root / "Solution.lean").write_text("import LeanSphincs.Submission.Scheme\n")
            for code in ("@[init LeanSphincs.Submission.f]\nopaque LeanSphincs.Submission.m : Unit\n",
                         "attribute [init LeanSphincs.Submission.f] LeanSphincs.Submission.m\n",
                         "@[builtin_init LeanSphincs.Submission.f]\nopaque LeanSphincs.Submission.m : Unit\n"):
                (root / "Scheme.lean").write_text("import LeanSphincs.Benchmark.Target\n" + code)
                result = subprocess.run(["bash", str(VERIFIER / "check-submission-imports.sh"),
                                         str(root)], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, code)
                self.assertIn("build-time execution", result.stderr)
            (root / "Scheme.lean").write_text(
                "import LeanSphincs.Benchmark.Target\ndef LeanSphincs.Submission.f (init : Nat) := init\n")
            result = subprocess.run(["bash", str(VERIFIER / "check-submission-imports.sh"),
                                     str(root)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
