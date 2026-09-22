"""verify.py exports only a flat submission root, checks the pin first and maps receipts faithfully."""
from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent
sys.path.insert(0, str(VERIFIER))
spec = importlib.util.spec_from_file_location("verify", VERIFIER / "verify.py")
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)

FILES = {"Scheme.lean": b"def x := 1\n", "Solution.lean": b"theorem t : True := trivial\n",
         "sigma.txt": b"2274\n", "hverify.txt": b"160\n", "bound.txt": b"[[4,1,1,0,128]]\n",
         "NOTES.md": b"# Idea\nshorter chains\n"}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, text=True,
                          env={**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                               "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}).stdout.strip()


class VerifyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)
        self.cfg = verify.load_challenges()
        self.limits = self.cfg["limits"]
        self.track = verify.track(self.cfg, "full")
        self.repo = self.base / "repo"
        root = self.repo / self.track["submission_root"]
        root.mkdir(parents=True)
        for name, data in FILES.items():
            (root / name).write_bytes(data)
        (self.repo / "README.md").write_text("outside the root\n")
        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "add", "-A")
        git(self.repo, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "submission")
        self.sha = git(self.repo, "rev-parse", "HEAD")

    def tearDown(self):
        self.temp.cleanup()

    def test_track_metadata_matches_the_repository_contract(self):
        self.assertEqual(self.track["submission_root"], "formal/Submissions/Full")
        self.assertEqual(self.track["objective"], "sigma * hverify")
        self.assertEqual(self.cfg["lean_root"], "formal")
        self.assertEqual(self.cfg["contract"]["meter"], "rom256-input64-ceil-v1")
        self.assertEqual(self.cfg["contract"]["verifier"], "verifier/verify.py")
        self.assertEqual(set(self.track["required_files"]), set(FILES) - {"NOTES.md"})
        self.assertEqual(set(self.track["optional_files"]), {"NOTES.md", "README.md"})
        for path in self.cfg["protected"]:
            self.assertTrue((ROOT / path).exists(), path)
        self.assertTrue((ROOT / self.cfg["contract"]["pin_file"]).is_file())
        self.assertIn("formal/LeanSphincs/Benchmark/Availability.lean", self.cfg["protected"])
        benchmark = {f"formal/LeanSphincs/Benchmark/{p.name}" for p in (ROOT / "formal/LeanSphincs/Benchmark").glob("*.lean")
                     if p.name != "Challenge.lean"}
        self.assertLessEqual(benchmark, set(self.cfg["protected"]), "every statement module must be protected")

    def test_pin_matches_the_checkout(self):
        verify.check_pin()
        self.assertEqual(verify.contract_id(self.cfg),
                         hashlib.sha256((ROOT / self.cfg["contract"]["pin_file"]).read_bytes()).hexdigest())

    def test_export_takes_only_the_root_from_the_exact_commit(self):
        dest = self.base / "staged"
        full = verify.export_root(str(self.repo), self.sha, self.track["submission_root"], dest, self.limits)
        self.assertEqual(full, self.sha)
        self.assertEqual(sorted(p.name for p in dest.iterdir()), sorted(FILES))
        self.assertEqual((dest / "sigma.txt").read_bytes(), b"2274\n")
        self.assertEqual((dest / "README.md").exists(), False)
        self.assertEqual(verify.read_notes(dest), "# Idea\nshorter chains\n")

    def test_export_from_a_worktree_without_commit(self):
        dest = self.base / "staged-wt"
        self.assertEqual(verify.export_root(str(self.repo), None, self.track["submission_root"], dest, self.limits),
                         "worktree")
        self.assertEqual(sorted(p.name for p in dest.iterdir()), sorted(FILES))

    def test_notes_are_capped_and_never_followed(self):
        dest = self.base / "notes"
        dest.mkdir()
        (dest / "NOTES.md").write_bytes(b"x" * (verify.NOTES_CAP + 10))
        self.assertEqual(len(verify.read_notes(dest)), verify.NOTES_CAP)
        (dest / "NOTES.md").unlink()
        (dest / "NOTES.md").symlink_to("/etc/hostname")
        self.assertIsNone(verify.read_notes(dest))
        self.assertIsNone(verify.read_notes(self.base))

    def test_nested_directories_symlinks_and_hidden_files_are_rejected(self):
        root = self.repo / self.track["submission_root"]
        (root / "nested").mkdir()
        (root / "nested" / "Deep.lean").write_text("-- nested\n")
        git(self.repo, "add", "-A")
        git(self.repo, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "nested")
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), git(self.repo, "rev-parse", "HEAD"), self.track["submission_root"],
                               self.base / "s1", self.limits)
        (root / "nested" / "Deep.lean").unlink()
        (root / "nested").rmdir()
        os.symlink("/etc/hostname", root / "Link.lean")
        git(self.repo, "add", "-A")
        git(self.repo, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "symlink")
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), git(self.repo, "rev-parse", "HEAD"), self.track["submission_root"],
                               self.base / "s2", self.limits)
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), None, self.track["submission_root"], self.base / "s3", self.limits)
        os.unlink(root / "Link.lean")
        (root / ".hidden").write_text("x")
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), None, self.track["submission_root"], self.base / "s4", self.limits)

    def test_size_limits_and_missing_root_are_rejected(self):
        small = dict(self.limits, max_total_bytes=10)
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), self.sha, self.track["submission_root"], self.base / "s5", small)
        with self.assertRaises((verify.Reject, verify.Failure)):
            verify.export_root(str(self.repo), self.sha, "formal/Submissions/Other", self.base / "s6", self.limits)
        with self.assertRaises(verify.Reject):
            verify.export_root(str(self.repo), "--upload-pack=evil", self.track["submission_root"],
                               self.base / "s7", self.limits)

    def accepted(self, **changes):
        report = {"status": "accepted", "claim_version": "claim-v2", "hash_meter": {"id": "rom256-input64-ceil-v1"},
                  "metrics": {"sigma": 2274, "hverify": 160, "bound": [[4, 1, 1, 0, 128]]},
                  "score": {"value": str(2274 * 160)}, "comparator_exit": 0, "compilation_exit": 0}
        report.update(changes)
        return report

    def test_accepted_receipt_becomes_verified_with_consistent_metrics(self):
        result = verify.interpret(self.accepted(), "full", self.sha, self.limits)
        self.assertEqual(result["status"], "verified")
        self.assertEqual((result["sigma"], result["hverify"], result["score"]), (2274, 160, "363840"))
        self.assertEqual(result["bound"], [[4, 1, 1, 0, 128]])
        self.assertEqual(result["hash_meter"], "rom256-input64-ceil-v1")
        self.assertFalse(result["ranked"])

    def test_inconsistent_accepted_receipts_are_failures_not_verdicts(self):
        for changes in ({"score": {"value": "1"}}, {"metrics": {"sigma": 0, "hverify": 160}},
                        {"metrics": {"sigma": "2274", "hverify": 160}},
                        {"metrics": {"sigma": self.limits["max_metric"] + 1, "hverify": 1}}):
            with self.assertRaises(verify.Failure):
                verify.interpret(self.accepted(**changes), "full", self.sha, self.limits)

    def test_other_statuses_map_onto_the_service_vocabulary(self):
        run = self.base / "run"
        run.mkdir()
        (run / "comparator.log").write_text("theorem statement do not match\n")
        (run / "compile.log").write_text("error: unknown identifier\n")
        rejected = verify.interpret({"status": "verification_failed", "comparator_exit": 1, "compilation_exit": 0},
                                    "full", self.sha, self.limits, run)
        self.assertEqual(rejected["status"], "rejected")
        self.assertIn("comparator rejected", rejected["reason"])
        self.assertIn("theorem statement do not match", rejected["tail"])
        compile_failed = verify.interpret({"status": "verification_failed", "compilation_exit": 1}, "full", self.sha,
                                          self.limits, run)
        self.assertEqual(compile_failed["status"], "rejected")
        self.assertIn("did not compile", compile_failed["reason"])
        self.assertIn("unknown identifier", compile_failed["tail"])
        policy = verify.interpret({"status": "source_rejected", "error": "missing submission artifacts: bound.txt"},
                                  "full", self.sha, self.limits)
        self.assertEqual((policy["status"], policy["errors"]), ("policy_rejected", ["missing submission artifacts: bound.txt"]))
        timeout = verify.interpret({"status": "timed_out", "limit_seconds": 5400, "error": "compilation exceeded the 5400 second budget"},
                                   "full", self.sha, self.limits)
        self.assertEqual((timeout["status"], timeout["limit_s"]), ("timeout", 5400))
        busy = verify.interpret({"status": "worker_busy"}, "full", self.sha, self.limits)
        self.assertEqual((busy["status"], busy["retryable"]), ("failed", True))
        interrupted = verify.interpret({"status": "interrupted"}, "full", self.sha, self.limits)
        self.assertEqual((interrupted["status"], interrupted["retryable"]), ("failed", True))
        infra = verify.interpret({"status": "infrastructure_error", "error": "disk"}, "full", self.sha, self.limits)
        self.assertEqual((infra["status"], infra["reason"], infra["retryable"]), ("failed", "disk", False))
        for result in (rejected, policy, timeout, busy, infra):
            self.assertFalse(result["ranked"])
            self.assertNotIn("score", result)

    def run_cli(self, *args, work=None):
        work = work or self.base / "work"
        proc = subprocess.run([sys.executable, str(VERIFIER / "verify.py"), "full", "--source", str(self.repo),
                               "--json", "--work", str(work), *args], capture_output=True, text=True, cwd=ROOT)
        return proc, json.loads(proc.stdout)

    def test_cli_rejects_a_missing_commit_without_running_the_verifier(self):
        proc, result = self.run_cli("--commit", self.sha[:7] + "0")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["contract"], verify.contract_id(self.cfg))
        self.assertEqual(result["track"], "full")
        self.assertFalse(result["ranked"])
        self.assertTrue(result["finished_at"].endswith("Z"))
        self.assertIsInstance(result["duration_s"], float)
        self.assertTrue(Path(result["log"]).is_file())

    def test_cli_refuses_a_checkout_that_differs_from_its_pin(self):
        output = io.StringIO()
        argv = ["verify.py", "full", "--source", str(self.repo), "--commit", self.sha, "--json",
                "--work", str(self.base / "pinwork")]
        failure = verify.Failure("protected files differ from the contract pin: verify.py")
        with patch.object(sys, "argv", argv), patch.object(verify.signal, "signal"), \
                patch.object(verify, "check_pin", side_effect=failure), \
                patch.object(verify, "export_root") as export, patch.object(verify, "run_verifier") as runner, \
                contextlib.redirect_stdout(output):
            self.assertEqual(verify.main(), 1)
        export.assert_not_called()
        runner.assert_not_called()
        result = json.loads(output.getvalue())
        self.assertEqual(result["status"], "failed")
        self.assertIn("differ from the contract pin", result["reason"])
        self.assertNotIn("contract", result)

    def test_pin_check_detects_a_tampered_protected_file(self):
        trusted = self.base / "trusted"
        for rel in self.cfg["protected"] + [self.cfg["contract"]["pin_file"]]:
            (trusted / rel).parent.mkdir(parents=True, exist_ok=True)
            (trusted / rel).write_bytes((ROOT / rel).read_bytes())
        verify.check_pin(trusted)
        (trusted / "verifier/comparator.json").write_text("{}")
        with self.assertRaisesRegex(verify.Failure, "comparator.json"):
            verify.check_pin(trusted)

    def test_archive_is_written_before_the_verifier_and_restored_on_retry(self):
        store = self.base / "sources"
        sid = "a" * 32
        output = io.StringIO()
        receipt_dir = self.base / "receipt"
        receipt_dir.mkdir()
        (receipt_dir / "result.json").write_text(json.dumps({"status": "source_rejected", "error": "fixture"}))
        argv = ["verify.py", "full", "--source", str(self.repo), "--commit", self.sha, "--json", "--keep",
                "--work", str(self.base / "w1"), "--archive-dir", str(store), "--archive-id", sid]
        with patch.object(sys, "argv", argv), patch.object(verify.signal, "signal"), \
                patch.object(verify, "run_verifier", return_value=({"status": "source_rejected"}, receipt_dir)) as runner, \
                contextlib.redirect_stdout(output):
            self.assertEqual(verify.main(), 1)
        result = json.loads(output.getvalue())
        self.assertEqual(result["status"], "policy_rejected")
        self.assertEqual(result["commit"], self.sha)
        self.assertEqual(result["notes"], FILES["NOTES.md"].decode())
        archive = result["source_archive"]
        self.assertEqual((archive["commit"], archive["track"], archive["contract"], archive["submission_root"]),
                         (self.sha, "full", verify.contract_id(self.cfg), "formal/Submissions/Full"))
        self.assertEqual(archive["file_count"], len(FILES))
        self.assertTrue((store / f"{archive['sha256']}.zip").is_file())
        runner.assert_called_once()
        staged = runner.call_args.args[0]
        self.assertEqual(sorted(p.name for p in staged.iterdir()), sorted(FILES))
        # A retry restores from the store without reading the repository.
        output = io.StringIO()
        argv[argv.index("--work") + 1] = str(self.base / "w2")
        with patch.object(sys, "argv", argv), patch.object(verify.signal, "signal"), \
                patch.object(verify, "export_root") as export, \
                patch.object(verify, "run_verifier", return_value=({"status": "source_rejected"}, receipt_dir)), \
                contextlib.redirect_stdout(output):
            verify.main()
        export.assert_not_called()
        retry = json.loads(output.getvalue())
        self.assertEqual(retry["source_archive"], archive)
        self.assertEqual(sorted(p.name for p in (self.base / "w2/staged").iterdir()), sorted(FILES))

    def test_archive_failure_prevents_any_candidate_verification(self):
        output = io.StringIO()
        argv = ["verify.py", "full", "--source", str(self.repo), "--commit", self.sha, "--json",
                "--work", str(self.base / "w3"), "--archive-dir", str(self.base / "sources"), "--archive-id", "b" * 32]
        with patch.object(sys, "argv", argv), patch.object(verify.signal, "signal"), \
                patch.object(verify, "save_source", side_effect=verify.ArchiveError("archive unavailable")), \
                patch.object(verify, "run_verifier") as runner, contextlib.redirect_stdout(output):
            self.assertEqual(verify.main(), 1)
        runner.assert_not_called()
        result = json.loads(output.getvalue())
        self.assertEqual((result["status"], result["retryable"]), ("failed", False))
        self.assertIn("archive unavailable", result["reason"])

    def test_archive_requires_the_exact_resolved_commit(self):
        proc, result = self.run_cli("--commit", self.sha[:12], "--archive-dir", str(self.base / "sources"),
                                    "--archive-id", "c" * 32)
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(result["status"], "failed")
        self.assertIn("exact resolved commit", result["reason"])
        self.assertFalse((self.base / "sources").exists())

    def test_hidden_directories_are_recorded(self):
        hidden = self.base / "private"
        hidden.mkdir()
        proc, result = self.run_cli("--commit", self.sha[:7] + "0", "--hide", str(hidden), "--keep")
        self.assertIn("hidden from the proof", Path(result["log"]).read_text())


if __name__ == "__main__":
    unittest.main()
