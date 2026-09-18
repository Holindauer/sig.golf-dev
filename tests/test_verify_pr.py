"""verify_pr.py exports only a flat submission root and maps receipts faithfully."""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("verify_pr", ROOT / "scripts/verify_pr.py")
verify_pr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify_pr)

FILES = {"Scheme.lean": b"def x := 1\n", "Solution.lean": b"theorem t : True := trivial\n",
         "sigma.txt": b"2274\n", "hverify.txt": b"160\n", "bound.txt": b"[[4,1,1,0,128]]\n"}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, text=True,
                          env={**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                               "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}).stdout.strip()


class VerifyPrTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)
        self.cfg = verify_pr.load_challenges()
        self.limits = self.cfg["limits"]
        self.track = verify_pr.track(self.cfg, "full")
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
        self.assertEqual(self.track["submission_root"], "submissions/full")
        self.assertEqual(self.track["objective"], "sigma * hverify")
        self.assertEqual(self.cfg["contract"]["meter"], "rom256-input64-ceil-v1")
        self.assertEqual(set(self.track["required_files"]), set(FILES))
        for path in self.cfg["protected"]:
            self.assertTrue((ROOT / path).exists(), path)

    def test_export_takes_only_the_root_from_the_exact_commit(self):
        dest = self.base / "staged"
        full = verify_pr.export_root(str(self.repo), self.sha, self.track["submission_root"], dest, self.limits)
        self.assertEqual(full, self.sha)
        self.assertEqual(sorted(p.name for p in dest.iterdir()), sorted(FILES))
        self.assertEqual((dest / "sigma.txt").read_bytes(), b"2274\n")
        self.assertFalse((dest / "README.md").exists())

    def test_export_from_a_worktree_without_commit(self):
        dest = self.base / "staged-wt"
        self.assertEqual(verify_pr.export_root(str(self.repo), None, self.track["submission_root"], dest, self.limits),
                         "worktree")
        self.assertEqual(sorted(p.name for p in dest.iterdir()), sorted(FILES))

    def test_nested_directories_symlinks_and_hidden_files_are_rejected(self):
        root = self.repo / self.track["submission_root"]
        (root / "nested").mkdir()
        (root / "nested" / "Deep.lean").write_text("-- nested\n")
        git(self.repo, "add", "-A")
        git(self.repo, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "nested")
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), git(self.repo, "rev-parse", "HEAD"), self.track["submission_root"],
                                  self.base / "s1", self.limits)
        (root / "nested" / "Deep.lean").unlink()
        (root / "nested").rmdir()
        os.symlink("/etc/hostname", root / "Link.lean")
        git(self.repo, "add", "-A")
        git(self.repo, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "symlink")
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), git(self.repo, "rev-parse", "HEAD"), self.track["submission_root"],
                                  self.base / "s2", self.limits)
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), None, self.track["submission_root"], self.base / "s3", self.limits)
        os.unlink(root / "Link.lean")
        (root / ".hidden").write_text("x")
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), None, self.track["submission_root"], self.base / "s4", self.limits)

    def test_size_limits_and_missing_root_are_rejected(self):
        small = dict(self.limits, max_total_bytes=10)
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), self.sha, self.track["submission_root"], self.base / "s5", small)
        with self.assertRaises((verify_pr.Reject, verify_pr.Failure)):
            verify_pr.export_root(str(self.repo), self.sha, "submissions/other", self.base / "s6", self.limits)
        with self.assertRaises(verify_pr.Reject):
            verify_pr.export_root(str(self.repo), "--upload-pack=evil", self.track["submission_root"],
                                  self.base / "s7", self.limits)

    def accepted(self, **changes):
        report = {"status": "accepted", "claim_version": "claim-v2", "hash_meter": {"id": "rom256-input64-ceil-v1"},
                  "metrics": {"sigma": 2274, "hverify": 160, "bound": [[4, 1, 1, 0, 128]]},
                  "score": {"value": str(2274 * 160)}, "comparator_exit": 0, "compilation_exit": 0}
        report.update(changes)
        return report

    def test_accepted_receipt_becomes_verified_with_consistent_metrics(self):
        result = verify_pr.interpret(self.accepted(), "full", self.sha, self.limits)
        self.assertEqual(result["status"], "verified")
        self.assertEqual((result["sigma"], result["hverify"], result["score"]), (2274, 160, "363840"))
        self.assertEqual(result["hash_meter"], "rom256-input64-ceil-v1")
        self.assertFalse(result["ranked"])

    def test_inconsistent_accepted_receipts_are_failures_not_verdicts(self):
        for changes in ({"score": {"value": "1"}}, {"metrics": {"sigma": 0, "hverify": 160}},
                        {"metrics": {"sigma": "2274", "hverify": 160}},
                        {"metrics": {"sigma": self.limits["max_metric"] + 1, "hverify": 1}}):
            with self.assertRaises(verify_pr.Failure):
                verify_pr.interpret(self.accepted(**changes), "full", self.sha, self.limits)

    def test_other_statuses_map_to_rejected_or_failed(self):
        run = self.base / "run"
        run.mkdir()
        (run / "comparator.log").write_text("theorem statement do not match\n")
        rejected = verify_pr.interpret({"status": "verification_failed", "comparator_exit": 1, "compilation_exit": 0},
                                       "full", self.sha, self.limits, run)
        self.assertEqual(rejected["status"], "rejected")
        self.assertIn("theorem statement do not match", rejected["reason"])
        source = verify_pr.interpret({"status": "source_rejected", "error": "missing submission artifacts: bound.txt"},
                                     "full", self.sha, self.limits)
        self.assertEqual((source["status"], source["reason"]), ("rejected", "missing submission artifacts: bound.txt"))
        busy = verify_pr.interpret({"status": "worker_busy"}, "full", self.sha, self.limits)
        self.assertEqual((busy["status"], busy.get("retryable")), ("failed", True))
        self.assertEqual(verify_pr.interpret({"status": "infrastructure_error", "error": "disk"}, "full", self.sha,
                                             self.limits)["status"], "failed")

    def test_cli_rejects_a_missing_root_without_running_the_verifier(self):
        proc = subprocess.run([str(ROOT / "scripts/verify_pr.py"), "full", "--source", str(self.repo),
                               "--commit", self.sha[:7] + "0", "--json"], capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(proc.returncode, 1)
        self.assertIn(json.loads(proc.stdout)["status"], {"failed", "rejected"})


if __name__ == "__main__":
    unittest.main()
