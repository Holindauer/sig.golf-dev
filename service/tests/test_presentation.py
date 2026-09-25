import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from presentation import PresentationError, validate_json, validate_svg

CLAIM = {'S': 10, 'W': 10, 'C': 100}


def encoded(value):
    return json.dumps(value).encode()


class PresentationTests(unittest.TestCase):
    def test_valid_profile_uses_total_counts(self):
        value = {'version': 1, 'summary': 'A small forest.', 'diagram': False,
                 'facts': [{'label': 'Digest', 'value': '256 bits'}],
                 'profile': {'samples': 2, 'method': 'Two fixed accepting messages',
                             'instructions': {'ADDI': 8, 'HALT': 2},
                             'hashes': {'192': 1, '768': 1}}}
        self.assertEqual(validate_json(encoded(value), CLAIM), value)

    def test_cycle_bound_catches_bad_profile(self):
        value = {'version': 1, 'summary': 'A small forest.',
                 'profile': {'samples': 1, 'method': 'One run',
                             'instructions': {'ADDI': 100, 'HALT': 1},
                             'hashes': {'192': 1}}}
        with self.assertRaisesRegex(PresentationError, 'exceed'):
            validate_json(encoded(value), CLAIM)

    def test_hash_rows_use_input_bit_length_for_cycles(self):
        value = {'version': 1, 'summary': 'A small forest.',
                 'profile': {'samples': 1, 'method': 'One accepting run',
                             'instructions': {'HALT': 1}, 'hashes': {'192': 1, '768': 1}}}
        self.assertEqual(validate_json(encoded(value), {'C': 25, 'W': 0}), value)
        with self.assertRaisesRegex(PresentationError, 'exceed'):
            validate_json(encoded(value), {'C': 24, 'W': 0})
        for bits in ('0192', '520'):
            value['profile']['hashes'] = {bits: 1}
            with self.assertRaisesRegex(PresentationError, 'bit length'):
                validate_json(encoded(value), {'C': 25, 'W': 0})

    def test_multiplication_division_and_witness_are_charged(self):
        value = {'version': 1, 'summary': 'A small forest.',
                 'profile': {'samples': 1, 'method': 'One accepting run',
                             'instructions': {'MUL': 1, 'REMUW': 1, 'ADD': 1, 'HALT': 1},
                             'hashes': {'512': 1}}}
        self.assertEqual(validate_json(encoded(value), {'C': 20, 'W': 257}), value)
        with self.assertRaisesRegex(PresentationError, 'exceed'):
            validate_json(encoded(value), {'C': 19, 'W': 257})

    def test_malformed_metadata_is_a_presentation_error(self):
        with self.assertRaises(PresentationError):
            validate_json(b'[' * 2000 + b']' * 2000, CLAIM)
        value = {'version': 1, 'summary': 'Example',
                 'profile': {'samples': 1, 'method': 'One run',
                             'instructions': {'HALT': 1}, 'hashes': {'1' * 5000: 1}}}
        with self.assertRaises(PresentationError):
            validate_json(encoded(value), CLAIM)

    def test_reject_active_svg(self):
        safe = b'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 100"><path d="M0 0L10 10" fill="#286ec4"/></svg>'
        validate_svg(safe)
        with self.assertRaisesRegex(PresentationError, 'forbidden'):
            validate_svg(safe.replace(b'<path ', b'<script>alert(1)</script><path '))
        with self.assertRaisesRegex(PresentationError, 'DTD'):
            validate_svg(b'<!DOCTYPE svg [<!ENTITY x "hello">]>' + safe)
        with self.assertRaisesRegex(PresentationError, 'forbidden'):
            validate_svg(safe.replace(b'fill="#286ec4"', b'fill="url(https://example.com/x)"'))


if __name__ == '__main__':
    unittest.main()
