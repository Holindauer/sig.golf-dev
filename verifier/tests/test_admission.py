"""Kernel-lock contention and verifier admission before candidate access."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import verify_submission
from worker_admission import WorkerBusy, worker_slot


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def test_contention_then_reuse_preserves_inode(self):
        with worker_slot(self.root):
            inode = (self.root / ".worker.lock").stat().st_ino
            with self.assertRaises(WorkerBusy):
                with worker_slot(self.root):
                    self.fail("second admission succeeded")
        with worker_slot(self.root):
            self.assertEqual((self.root / ".worker.lock").stat().st_ino, inode)

    def test_exception_releases_lock(self):
        with self.assertRaises(KeyboardInterrupt):
            with worker_slot(self.root):
                raise KeyboardInterrupt()
        with worker_slot(self.root):
            pass

    def test_exec_child_does_not_keep_lock_alive(self):
        with worker_slot(self.root):
            child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"],
                                     close_fds=False)
        try:
            self.assertIsNone(child.poll())
            with worker_slot(self.root):
                pass
        finally:
            child.kill()
            child.wait(timeout=10)

    def test_symlink_rejected_without_touching_target(self):
        target = self.root / "target"
        target.write_text("unchanged")
        (self.root / ".worker.lock").symlink_to(target)
        with self.assertRaises(OSError):
            with worker_slot(self.root):
                self.fail("symlink admitted")
        self.assertEqual(target.read_text(), "unchanged")

    def test_fifo_rejected_without_blocking(self):
        os.mkfifo(self.root / ".worker.lock")
        with self.assertRaisesRegex(RuntimeError, "regular file"):
            with worker_slot(self.root):
                self.fail("FIFO admitted")

    def test_busy_receipt_precedes_candidate_access(self):
        results = self.root / "benchmark-results/runs"
        results.mkdir(parents=True)
        with patch.object(verify_submission, "ROOT", self.root), \
             patch.object(verify_submission, "capture") as capture, worker_slot(results):
            report, directory = verify_submission.verify(self.root / "missing")
        capture.assert_not_called()
        self.assertEqual(report["status"], "worker_busy")
        self.assertEqual(report["stage"], "admission")
        self.assertTrue(report["retryable"])
        self.assertEqual(report["hash_meter"]["id"], "rom256-input64-ceil-v1")
        self.assertFalse(report["ranked"])
        self.assertNotIn("score", report)
        self.assertNotIn("submission", report)
        self.assertEqual(json.loads((directory / "result.json").read_text()), report)
        with patch.object(verify_submission, "ROOT", self.root):
            retry, _ = verify_submission.verify(self.root / "missing")
        self.assertEqual(retry["status"], "source_rejected")

    def test_lock_covers_receipt_publication(self):
        original = verify_submission.write_receipt

        def publish(path, report):
            with self.assertRaises(WorkerBusy):
                with worker_slot(path.parent.parent):
                    self.fail("lock released before receipt publication")
            original(path, report)

        with patch.object(verify_submission, "ROOT", self.root), \
             patch.object(verify_submission, "write_receipt", side_effect=publish):
            verify_submission.verify(self.root / "missing")

    def test_killed_owner_releases_kernel_lock(self):
        script = """
import sys, time
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from worker_admission import worker_slot
with worker_slot(Path(sys.argv[2])):
    print('locked', flush=True)
    time.sleep(60)
"""
        with tempfile.TemporaryFile(mode="w+") as ready:
            process = subprocess.Popen([sys.executable, "-c", script, str(SCRIPTS), str(self.root)],
                                       stdout=ready, stderr=subprocess.PIPE)
            try:
                # Bounded readiness polling uses flushed output, not a PID file.
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    ready.seek(0)
                    if ready.read().strip() == "locked":
                        break
                    if process.poll() is not None:
                        self.fail("owner exited before acquiring lock")
                    time.sleep(0.01)
                else:
                    self.fail("owner did not acquire lock")
                with self.assertRaises(WorkerBusy):
                    with worker_slot(self.root):
                        self.fail("cross-process contention failed")
                process.kill()
                process.communicate(timeout=10)
                with worker_slot(self.root):
                    pass
            finally:
                if process.poll() is None:
                    process.kill()
                process.communicate()


if __name__ == "__main__":
    unittest.main()
