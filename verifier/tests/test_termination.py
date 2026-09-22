"""CLI signal policy and real process-group cleanup, without Lean compilation."""

import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import MagicMock, patch

SCRIPTS = Path(__file__).resolve().parents[1]   # verifier/
sys.path.insert(0, str(SCRIPTS))
import verify_submission
from verify_submission import termination_as_interrupt


class TerminationTests(unittest.TestCase):
    def test_handler_restored_after_normal_exit(self):
        previous = signal.getsignal(signal.SIGTERM)
        with termination_as_interrupt():
            self.assertNotEqual(signal.getsignal(signal.SIGTERM), previous)
        self.assertEqual(signal.getsignal(signal.SIGTERM), previous)

    def test_repeated_termination_does_not_interrupt_cleanup(self):
        previous = signal.getsignal(signal.SIGTERM)
        with termination_as_interrupt():
            with self.assertRaises(KeyboardInterrupt):
                os.kill(os.getpid(), signal.SIGTERM)
            self.assertEqual(signal.getsignal(signal.SIGTERM), signal.SIG_IGN)
            os.kill(os.getpid(), signal.SIGTERM)
        self.assertEqual(signal.getsignal(signal.SIGTERM), previous)

    def test_sigterm_kills_active_worker_group(self):
        driver = """
import os, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from verify_submission import run, termination_as_interrupt
root = Path(sys.argv[2])
with termination_as_interrupt():
    try:
        run([sys.executable, '-c',
             'import os, time; print(os.getpid(), flush=True); time.sleep(60)'],
            root, dict(os.environ), root / 'worker.log')
    except KeyboardInterrupt:
        print('cleanup completed', flush=True)
        sys.exit(23)
"""
        with tempfile.TemporaryDirectory() as directory:
            process = subprocess.Popen([sys.executable, "-c", driver, str(SCRIPTS), directory],
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            worker = None
            try:
                log = Path(directory) / "worker.log"
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    if log.exists() and log.read_text().strip():
                        worker = int(log.read_text().strip())
                        break
                    if process.poll() is not None:
                        self.fail(f"driver exited early: {process.communicate()}")
                    time.sleep(0.01)
                self.assertIsNotNone(worker, "worker did not become ready")
                process.terminate()
                stdout, stderr = process.communicate(timeout=10)
                self.assertEqual(process.returncode, 23, stderr)
                self.assertIn("cleanup completed", stdout)
                with self.assertRaises(ProcessLookupError):
                    os.killpg(worker, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                process.communicate()
                if worker is not None:
                    try:
                        os.killpg(worker, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_cancellation_stops_named_service_before_client_cleanup(self):
        for stop_error in (None, subprocess.TimeoutExpired("systemctl", 15)):
            with self.subTest(stop_error=stop_error), tempfile.TemporaryDirectory() as directory:
                worker = MagicMock(pid=12345)
                worker.wait.side_effect = [KeyboardInterrupt(), 0]
                events = []

                def stop(command, **kwargs):
                    events.append(("stop", command))
                    if stop_error:
                        raise stop_error
                    return subprocess.CompletedProcess(command, 0, "LoadState=not-found\nActiveState=inactive\nControlGroup=\n", "")

                with patch.object(verify_submission.subprocess, "Popen", return_value=worker), \
                     patch.object(verify_submission.subprocess, "run", side_effect=stop), \
                     patch.object(verify_submission.os, "killpg",
                                  side_effect=lambda *args: events.append(("kill", args))):
                    with self.assertRaises(subprocess.TimeoutExpired if stop_error else KeyboardInterrupt):
                        verify_submission.run(
                            ["systemd-run", "--unit=leansphincs-test.service", "--", "worker"],
                            Path(directory), {}, Path(directory) / "log")
                self.assertEqual(events[0],
                    ("stop", ["systemctl", "--user", "stop", "leansphincs-test.service"]))
                self.assertEqual(events[-1], ("kill", (12345, signal.SIGKILL)))
                self.assertEqual(len(events), 2 if stop_error else 3)
                self.assertEqual(worker.wait.call_count, 2)


if __name__ == "__main__":
    unittest.main()
