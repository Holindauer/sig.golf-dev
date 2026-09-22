"""Only the known comparator patch may be migrated automatically."""
from pathlib import Path
import subprocess
import tempfile
import unittest

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent

class SetupMigrationTests(unittest.TestCase):
    def test_recognized_previous_patch_migrates_and_other_edits_fail(self):
        tool = VERIFIER / '.tools/comparator'
        if not tool.exists():
            self.skipTest('pinned comparator source unavailable; setup integration required')
        original = subprocess.check_output(['git', '-C', str(tool), 'show', 'HEAD:Main.lean'])
        setup = (VERIFIER / 'setup_tools.sh').read_text()
        function = setup[setup.index('clone_at() {'):setup.index('\nclone_at https://')]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / 'tool'
            repo.mkdir()
            subprocess.run(['git', 'init', '-q', str(repo)], check=True)
            (repo / 'Main.lean').write_bytes(original)
            subprocess.run(['git', '-C', str(repo), 'add', 'Main.lean'], check=True)
            subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Fixture',
                            '-c', 'user.email=fixture@example.invalid',
                            'commit', '--no-gpg-sign', '-qm', 'fixture'], check=True)
            revision = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
            def check():
                return subprocess.run(['bash', '-c',
                    'set -euo pipefail\ncomparator_dir="$1"\n' + function +
                    '\nclone_at unused "$2" "$1"\n', 'test', str(repo), revision],
                    cwd=ROOT, capture_output=True, text=True)
            for patch_name in ('comparator-leanchecker-v1.patch', 'comparator-leanchecker.patch'):
                subprocess.run(['git', '-C', str(repo), 'apply', str(VERIFIER / patch_name)], check=True)
                self.assertEqual(check().returncode, 0)
                if patch_name.endswith('v1.patch'):
                    self.assertEqual((repo / 'Main.lean').read_bytes(), original)
                else:
                    with (repo / 'Main.lean').open('a') as stream: stream.write('\n-- unrelated edit\n')
                    self.assertNotEqual(check().returncode, 0)
            (repo / 'Main.lean').write_bytes(original)
            (repo / 'unexpected').write_text('unrelated file')
            self.assertNotEqual(check().returncode, 0)
            (repo / 'unexpected').unlink()
            subprocess.run(['git', '-C', str(repo), 'apply',
                str(VERIFIER / 'comparator-leanchecker-v1.patch')], check=True)
            subprocess.run(['git', '-C', str(repo), 'add', 'Main.lean'], check=True)
            self.assertNotEqual(check().returncode, 0)
