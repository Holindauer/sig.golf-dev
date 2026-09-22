from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from polynomial_annex import keygen_estimates


class PolynomialAnnexTests(unittest.TestCase):
    def test_paper_and_remetered_keygen(self):
        result = keygen_estimates()
        self.assertEqual(result["paper_keygen_units"], 405)
        self.assertEqual(result["rom32_keygen"], {"seed_expansion_units": 128,
            "row_units": 512, "parent_units": 170, "total_units": 810})
        self.assertEqual(result["hash_meter"]["id"], "rom256-input64-ceil-v1")
        self.assertFalse(result["ranked"])
        self.assertFalse(result["costs_certified"])
        self.assertFalse(result["security_proved"])

    def test_arithmetic_is_not_free_or_called_cycles(self):
        result = keygen_estimates()
        self.assertEqual(result["naive_horner"]["field_multiplications"], 1032192)
        self.assertEqual(result["naive_horner"]["field_additions"], 1032192)
        self.assertEqual(result["table_bytes"], 16384)
        self.assertNotIn("cycles", result)


if __name__ == "__main__":
    unittest.main()
