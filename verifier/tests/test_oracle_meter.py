"""v0.15 host-meter boundaries; Lean checks the corresponding oracle queries."""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from oracle_meter import hash_weight, meter_metadata


class OracleMeterTests(unittest.TestCase):
    def test_boundaries(self):
        for size, units in [(0, 0), (1, 1), (32, 1), (33, 1), (63, 1), (64, 1),
                            (65, 2), (96, 2), (127, 2), (128, 2), (129, 3)]:
            with self.subTest(size=size):
                self.assertEqual(hash_weight(size), units)

    def test_exact_ceiling_including_large_integers(self):
        for size in [*range(2049), 2**63 - 1, 2**256 + 1]:
            quotient, remainder = divmod(size, 64)
            self.assertEqual(hash_weight(size), quotient + bool(remainder))

    def test_no_float_negative_or_boolean_lengths(self):
        for size in [-1, 1.5, True, "64"]:
            with self.assertRaises(ValueError):
                hash_weight(size)

    def test_metadata_identifies_breaking_meter_change(self):
        self.assertEqual(meter_metadata(), {"id": "rom256-input64-ceil-v1",
            "input_unit_bytes": 64, "output_bytes": 32, "rounding": "ceil",
            "empty_input_cost": 0, "domain_separation_bytes_charged": True})

    def test_pr19_source_level_recalculation(self):
        # Pinned byte layouts in PR19_REVIEW.md, not a verification-cost proof.
        calls_and_bytes = [(1, 96), (14, 48), (140, 64), (1, 256), (3, 52),
                           (309, 48), (3, 704), (26, 64)]
        self.assertEqual(sum(calls for calls, _ in calls_and_bytes), 497)
        self.assertEqual(sum(calls * hash_weight(size) for calls, size in calls_and_bytes), 531)


if __name__ == "__main__":
    unittest.main()
