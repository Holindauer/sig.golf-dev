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
        (self.root / 'claim.json').write_text(json.dumps({'S': 8, 'W': 8, 'C': 100}))

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
        (self.root / 'claim.json').write_text(json.dumps({'S': 1 << 25, 'W': 0, 'C': 1}))
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('exceed the 16 MiB memory layout', value['errors'][0])


if __name__ == '__main__':
    unittest.main()
