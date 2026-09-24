import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'SigGolfCandidate').mkdir()
        (self.root / 'Solution.lean').write_text('import SigGolfCandidate.Helper\n')
        (self.root / 'SigGolfCandidate' / 'Helper.lean').write_text('import SigGolf\n')
        self.claim = {'S': 8, 'W': 8, 'C': 100,
                      'layout': {'message': 0, 'secret_key': 32, 'public_key': 64,
                                 'cache': 96, 'signature': 131168, 'witness': 131176}}
        self.write_claim()

    def write_claim(self):
        (self.root / 'claim.json').write_text(json.dumps(self.claim))

    def tearDown(self):
        self.temp.cleanup()

    def test_valid_layout_and_score(self):
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.assertEqual(value['score'], 800)

    def test_cross_import_is_rejected(self):
        (self.root / 'SigGolfCandidate' / 'Helper.lean').write_text('import SigGolfCandidateX.Helper\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

    def test_symlink_and_archive_file_are_rejected(self):
        (self.root / 'SigGolfCandidate' / 'Alias.lean').symlink_to('Helper.lean')
        (self.root / 'notes.zip').write_bytes(b'irrelevant')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertGreaterEqual(len(value['errors']), 2)

    def test_signature_must_fit_memory_layout(self):
        self.claim['S'] = 1 << 25
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('signature buffer exceeds 16 MiB memory', value['errors'][0])

    def test_overlapping_buffers_are_rejected(self):
        self.claim['layout']['signature'] = 96
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('cache and signature buffers overlap', value['errors'][0])

    def test_unaligned_offset_is_rejected(self):
        self.claim['layout']['message'] = 1
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('message offset is not 8-byte aligned', value['errors'][0])

    def test_empty_witness_may_share_an_address(self):
        self.claim['W'] = 0
        self.claim['layout']['witness'] = self.claim['layout']['cache']
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])

    def test_custom_layout_is_accepted(self):
        self.claim['layout'] = {'message': 0x40000, 'secret_key': 0x40100,
                                'public_key': 0x40200, 'cache': 0x80000,
                                'signature': 0x100000, 'witness': 0x100100}
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])


if __name__ == '__main__':
    unittest.main()
