import json
from pathlib import Path
import sys
import tempfile
import unittest

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent
sys.path.insert(0, str(VERIFIER))
from scoring_policy import product_score, load_scoring_profile, score_entry
from verify_submission import harness_manifest


class ScoringPolicyTests(unittest.TestCase):
    def test_profile_is_integrity_bound(self):
        self.assertIn("verifier/scoring.json", harness_manifest()["files"])

    def test_exact_product_and_tradeoffs(self):
        self.assertEqual(product_score(2, 3), 6)
        self.assertEqual(product_score(2**80, 7), 7 * 2**80)
        self.assertEqual(product_score(100, 200), product_score(200, 100))
        self.assertLess(product_score(99, 200), product_score(100, 200))

    def test_product_scores_without_price_but_never_confers_eligibility(self):
        profile = load_scoring_profile(VERIFIER / "scoring.json")
        self.assertNotIn("bandwidth_price", profile)
        score = score_entry(profile, 100, 200)
        self.assertEqual(score["value"], "20000")
        self.assertEqual(score["objective"], "signatureBytes * verification")
        self.assertEqual(score["tie_break"], 100)
        self.assertTrue(score["diagnostic"])
        self.assertFalse(score["eligible"])

    def test_old_profile_and_entrant_pricing_rejected(self):
        base = load_scoring_profile(VERIFIER / "scoring.json")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "scoring.json"
            for changes in ({"schema": "leansphincs-additive-profile-v1"},
                            {"bandwidth_price": None}, {"bandwidth_price": 1},
                            {"verification_meter": "other"}, {"id": ""}):
                path.write_text(json.dumps(base | changes))
                with self.assertRaises(ValueError): load_scoring_profile(path)

    def test_invalid_metrics_rejected(self):
        for args in ((0, 1), (1, 0), (-1, 1), (True, 1), (1, 0.5)):
            with self.assertRaises(ValueError): product_score(*args)
