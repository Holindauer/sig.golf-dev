"""Receipt state-machine tests, not cryptographic acceptance certificates.

The orchestration tests mock compilation/comparison. The separate real-comparator
canaries and SchemeClaim rejection suite remain necessary.
"""

from contextlib import ExitStack
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify_submission as verifier
from source_bundle import manifest, materialize


BUNDLE = {"Scheme.lean": b"", "Solution.lean": b"", "sigma.txt": b"2",
          "hverify.txt": b"3", "bound.txt": b"[[4,1,1,0,128]]"}


class IntegrityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        materialize(BUNDLE, self.root / "LeanSphincs/Submission")
        self.tool = self.root / "tool"
        self.tool.write_bytes(b"original tool")
        self.tools = {"test_tool": self.tool}
        self.report = {"submission": manifest(BUNDLE), "harness": {"sha256": "harness"},
                       "dependencies": {"library": "pin"},
                       "tools": {"test_tool": verifier.digest(self.tool)}}
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.harness = self.stack.enter_context(patch.object(
            verifier, "harness_manifest", return_value=self.report["harness"]))
        self.dependencies = self.stack.enter_context(patch.object(
            verifier, "check_dependencies", return_value=self.report["dependencies"]))

    def check(self):
        verifier.check_integrity(self.root, self.report, self.tools)

    def test_unchanged_evidence_passes(self):
        self.check()

    def test_docs_are_bound_by_the_receipt_but_absent_from_the_project(self):
        documented = BUNDLE | {"NOTES.md": b"# idea\n", "README.md": b"readme\n"}
        self.report["submission"] = manifest(documented)
        self.check()
        self.report["submission"] = manifest(documented | {"NOTES.md": b"# edited\n"})
        self.check()  # the project cannot see the docs, so only the Lean sources are compared
        self.report["submission"] = manifest(documented | {"Solution.lean": b"changed"})
        with self.assertRaisesRegex(RuntimeError, "snapshot changed"):
            self.check()

    def test_time_limit_receipt_carries_the_budget(self):
        report, _ = self.exercise_timeout()
        self.assertEqual(report["status"], "timed_out")
        self.assertEqual(report["limit_seconds"], 5400)
        self.assertIn("budget", report["error"])
        self.assertNotIn("score", report)

    def exercise_timeout(self):
        return OrchestrationTests().exercise([0, 0, subprocess.TimeoutExpired("compile", 1)])

    def test_changed_candidate_is_rejected(self):
        (self.root / "LeanSphincs/Submission/Solution.lean").write_bytes(b"changed")
        with self.assertRaisesRegex(RuntimeError, "snapshot changed"):
            self.check()

    def test_changed_harness_is_rejected(self):
        self.harness.return_value = {"sha256": "changed"}
        with self.assertRaisesRegex(RuntimeError, "harness changed"):
            self.check()

    def test_changed_dependency_is_rejected(self):
        self.dependencies.return_value = {"library": "other pin"}
        with self.assertRaisesRegex(RuntimeError, "dependencies changed"):
            self.check()

    def test_dirty_dependency_is_rejected(self):
        self.dependencies.side_effect = RuntimeError("tracked dependency changes: library")
        with self.assertRaisesRegex(RuntimeError, "tracked dependency changes"):
            self.check()

    def test_changed_tool_is_rejected(self):
        self.tool.write_bytes(b"replacement tool")
        with self.assertRaisesRegex(RuntimeError, "tool binaries changed"):
            self.check()

    def test_missing_tool_is_rejected(self):
        self.tool.unlink()
        with self.assertRaises(FileNotFoundError):
            self.check()


class PublicationTests(unittest.TestCase):
    def test_complete_receipt_and_private_permissions(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.json"
            verifier.write_receipt(path, {"status": "source_rejected", "ranked": False})
            self.assertEqual(json.loads(path.read_text())["status"], "source_rejected")
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)
            self.assertEqual(list(path.parent.glob(".receipt-*")), [])

    def test_failed_flush_or_replace_preserves_previous_receipt(self):
        for operation in ("fsync", "replace"):
            for existing in (False, True):
                with self.subTest(operation=operation, existing=existing), \
                     tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / "result.json"
                    if existing:
                        verifier.write_receipt(path, {"status": "old"})
                    with patch.object(verifier.os, operation, side_effect=OSError("disk failure")):
                        with self.assertRaisesRegex(OSError, "disk failure"):
                            verifier.write_receipt(path, {"status": "new"})
                    if existing:
                        self.assertEqual(json.loads(path.read_text()), {"status": "old"})
                    else:
                        self.assertFalse(path.exists())
                    self.assertEqual(list(path.parent.glob(".receipt-*")), [])


class OrchestrationTests(unittest.TestCase):
    def exercise(self, results, integrity_error=None):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            source = root / "input"
            materialize(BUNDLE, source)

            def prepare(project, bundle, rendered):
                materialize(bundle, project / "LeanSphincs/Submission")
                (project / ".lake/build/lib/lean/LeanSphincs/Benchmark").mkdir(parents=True)

            stack.enter_context(patch.object(verifier, "ROOT", root))
            stack.enter_context(patch.object(verifier.subprocess, "run",
                return_value=subprocess.CompletedProcess([], 0, "", "")))
            stack.enter_context(patch.object(verifier.subprocess, "check_output", return_value="/lean"))
            stack.enter_context(patch.object(verifier, "harness_manifest", return_value={}))
            stack.enter_context(patch.object(verifier, "verification_budget", return_value=5400))
            stack.enter_context(patch.object(verifier, "load_resource_profile", return_value={}))
            stack.enter_context(patch.object(verifier, "freeze_artifacts", return_value={}))
            stack.enter_context(patch.object(verifier, "load_scoring_profile", return_value={
                "id": "test-only"}))
            stack.enter_context(patch.object(verifier, "check_dependencies", return_value={}))
            stack.enter_context(patch.object(verifier, "digest", return_value="mock digest"))
            stack.enter_context(patch.object(verifier, "prepare_project", side_effect=prepare))
            stack.enter_context(patch.object(verifier, "run", side_effect=results))
            integrity = stack.enter_context(patch.object(verifier, "check_integrity",
                                                        side_effect=integrity_error))
            report, output = verifier.verify(source, insecure=True)
            self.assertEqual(json.loads((output / "result.json").read_text()), report)
            self.assertFalse(report["ranked"])
            return report, integrity.call_count

    def test_mock_success_issues_only_diagnostic_product(self):
        report, checks = self.exercise([0, 0, 0, 0])
        self.assertEqual(checks, 1)
        self.assertEqual(report["status"], "accepted")
        self.assertTrue(report["mathematical_verification"])
        self.assertFalse(report["deployment_eligible"])
        self.assertNotIn("current mathematical certificate missing", report["deployment_gates"]["reasons"])
        self.assertEqual(report["score"]["value"], "6")
        self.assertFalse(report["score"]["eligible"])
        self.assertTrue(report["score"]["diagnostic"])
        self.assertNotIn("score_pending", report)
        self.assertIn("lake", report["tools"])

    def test_mock_success_scores_only_after_integrity(self):
        report, checks = self.exercise([0, 0, 0, 0])
        self.assertEqual(checks, 1)
        self.assertEqual(report["score"]["value"], "6")

    def test_no_failure_path_issues_score(self):
        cases = [([1], None, "infrastructure_error", "trusted_build"),
                 ([0, 1], None, "infrastructure_error", "trusted_build"),
                 ([0, 0, 0, 1], None, "verification_failed", "integrity"),
                 ([0, 0, RuntimeError("service cleanup uncertain")], None,
                  "infrastructure_error", "compilation"),
                 ([0, 0, 0, subprocess.TimeoutExpired("comparator", 1)], None,
                  "timed_out", "comparison"),
                 ([0, 0, subprocess.TimeoutExpired("compile", 1)], None,
                  "timed_out", "compilation"),
                 ([0, 0, 0, KeyboardInterrupt()], None, "interrupted", "comparison"),
                 ([0, 0, 0, 0], RuntimeError("tool binaries changed"),
                  "infrastructure_error", "integrity"),
                 ([0, 0, 0, 0], FileNotFoundError("tool removed"),
                  "infrastructure_error", "integrity"),
                 ([0, 0, 0, 0], KeyboardInterrupt(), "interrupted", "integrity")]
        for results, error, status, stage in cases:
            with self.subTest(status=status, stage=stage, error=repr(error), results=repr(results)):
                report, _ = self.exercise(results, error)
                self.assertEqual(report["status"], status)
                self.assertEqual(report["stage"], stage)
                self.assertNotIn("score", report)


if __name__ == "__main__":
    unittest.main()
