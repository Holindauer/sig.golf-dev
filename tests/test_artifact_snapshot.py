"""Artifact bytes, substitution and cleanup are separate from source scanning."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from artifact_snapshot import capture_artifacts, freeze_artifacts
from source_bundle import manifest
import verify_submission as verifier

REL = '.lake/build/lib/lean/LeanSphincs/Submission'

class SnapshotTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.compiler, self.frozen = self.root / 'compiler', self.root / 'verification'
        for project in (self.compiler, self.frozen):
            (project / REL).mkdir(parents=True)
        self.file = self.compiler / REL / 'Solution.olean'
        self.file.write_bytes(b'checked bytes')
        self.addCleanup(lambda: (self.frozen / REL).chmod(0o700))

    def test_late_writes_and_substitution_do_not_change_snapshot(self):
        initial = freeze_artifacts(self.compiler, self.frozen, ['Solution'])
        self.file.write_bytes(b'delayed compiler output')
        self.file.unlink()
        self.file.symlink_to('/etc/passwd')
        self.assertEqual(manifest(capture_artifacts(self.frozen, ['Solution'])), initial)
        self.assertEqual((self.frozen / REL / 'Solution.olean').stat().st_mode & 0o777, 0o400)

    def test_snapshot_drift_is_detected(self):
        initial = freeze_artifacts(self.compiler, self.frozen, ['Solution'])
        artifact = self.frozen / REL / 'Solution.olean'
        artifact.chmod(0o600)  # trusted operator; sandbox cannot do this
        artifact.write_bytes(b'replacement')
        self.assertNotEqual(manifest(capture_artifacts(self.frozen, ['Solution'])), initial)

    def test_symlink_fifo_directory_and_unexpected_module_rejected(self):
        self.file.unlink()
        for kind in ('symlink', 'fifo', 'directory', 'unexpected'):
            with self.subTest(kind=kind):
                if kind == 'symlink': self.file.symlink_to('/etc/passwd')
                elif kind == 'fifo': os.mkfifo(self.file)
                elif kind == 'directory': self.file.mkdir()
                else: (self.compiler / REL / 'Other.olean').write_bytes(b'x')
                with self.assertRaises((OSError, RuntimeError)):
                    capture_artifacts(self.compiler, ['Solution'])
                if kind == 'directory': self.file.rmdir()
                elif kind == 'unexpected': (self.compiler / REL / 'Other.olean').unlink()
                else: self.file.unlink()

    def test_parent_directory_symlink_rejected(self):
        directory = self.compiler / REL
        directory.rename(directory.with_name('hidden'))
        directory.symlink_to(directory.with_name('hidden'), target_is_directory=True)
        with self.assertRaises(OSError): capture_artifacts(self.compiler, ['Solution'])

    def test_cleanup_uncertainty_fails_even_after_success(self):
        for state in ('', 'LoadState=loaded\nActiveState=active\nControlGroup=/test',):
            with self.subTest(state=state), patch.object(verifier.subprocess, 'run',
                    return_value=subprocess.CompletedProcess([], 0, state, '')):
                with self.assertRaisesRegex(RuntimeError, 'cleanup uncertain'):
                    verifier.stop_service('leansphincs-test.service', subprocess.DEVNULL)

    def test_no_build_in_prebuilt_comparator(self):
        patch_text = (Path(__file__).resolve().parents[1] / 'benchmark/comparator-leanchecker.patch').read_text()
        self.assertIn('unless prebuilt do safeLakeBuild challengeModule', patch_text)
        self.assertIn('unless prebuilt do safeLakeBuild solutionModule', patch_text)
        self.assertIn('--verify-prebuilt', patch_text)
