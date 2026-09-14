#!/usr/bin/env python3
"""Metric-only canaries in isolated projects under the real Linux sandbox.

The trusted test challenge is NOT SchemeClaim. This tests the sandboxed positive
path and metric matching, not cryptographic eligibility. No score is produced.
"""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from artifact_snapshot import capture_artifacts, freeze_artifacts
from source_bundle import manifest
from sandbox_profile import systemd_command
from verify_submission import ROOT, COMPARATOR, prepare_project, run


def main():
    lean = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    exporter = COMPARATOR / ".lake/packages/lean4export/.lake/build/bin/lean4export"
    landrun = ROOT / ".benchmark-tools/landrun/landrun"
    spec = importlib.util.spec_from_file_location("probe", ROOT / "scripts/check-sandbox.py")
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    print(json.dumps(probe.check(lean, exporter, landrun)), flush=True)
    output = ROOT / "benchmark-results"
    output.mkdir(exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="sandbox-canary-", dir=output))
    project = directory / "project"
    # Production candidate files are unused here. The test modules are copied
    # explicitly into the trusted organizer-only test project below.
    prepare_project(project, {}, "import LeanSphincs.Benchmark.Target\n")
    shutil.copytree(ROOT / "LeanSphincsTest", project / "LeanSphincsTest")
    shutil.copy2(ROOT / "LeanSphincsTest.lean", project / "LeanSphincsTest.lean")
    for facet in ("lib/lean", "ir"):
        (project / f".lake/build/{facet}/LeanSphincsTest/Submission").mkdir(parents=True)
    env = {"PATH": f"{lean}/bin:/usr/bin:/bin", "HOME": str(project / "home"),
           "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1",
           "COMPARATOR_LEAN4EXPORT": str(exporter),
           "COMPARATOR_LANDRUN": str(project / "strict-landrun.py")}
    if run([str(lean / "bin/lake"), "build", "LeanSphincsTest.Challenge"], project,
           env, directory / "trusted-build.log"):
        raise SystemExit(f"canary build failed: {directory}")
    config = json.loads((ROOT / "benchmark/comparator.json").read_text())
    config.update(challenge_module="LeanSphincsTest.Challenge", theorem_names=["LeanSphincsTest.candidate"],
                  definition_names=["LeanSphincsTest.Submission.scheme"])
    for case, expected in [("Good", "Your solution is okay!"),
                           ("WrongSigma", "theorem statement do not match"),
                           ("WrongMetrics", "theorem statement do not match"),
                           ("WrongBound", "theorem statement do not match"),
                           ("SmuggledAxiom", "Illegal axiom detected")]:
        config["solution_module"] = f"LeanSphincsTest.Submission.{case}"
        (project / "comparator.json").write_text(json.dumps(config))
        (project / "sandbox.json").write_text(json.dumps({"lean_prefix": str(lean), "exporter": str(exporter),
            "landrun": str(landrun), "submission_prefix": "LeanSphincsTest.Submission",
            "challenge_module": config["challenge_module"], "solution_module": config["solution_module"]}))
        compile_command = systemd_command([str(project / "strict-landrun.py"), "--",
            "lake", "build", config["solution_module"]], project, env)
        if run(compile_command, project, dict(os.environ), directory / f"{case}-compile.log"):
            raise RuntimeError(f"canary compilation failed: {case}")
        frozen = directory / (case + "-verification")
        prepare_project(frozen, {}, "import LeanSphincs.Benchmark.Target\n")
        shutil.copytree(ROOT / "LeanSphincsTest", frozen / "LeanSphincsTest")
        for namespace in ("LeanSphincs/Benchmark", "LeanSphincsTest"):
            shutil.copytree(project / ".lake/build/lib/lean" / namespace,
                frozen / ".lake/build/lib/lean" / namespace, dirs_exist_ok=True,
                ignore=shutil.ignore_patterns("Submission"))
        (frozen / ".lake/build/lib/lean/LeanSphincsTest/Submission").mkdir()
        modules = [p.stem for p in (ROOT / "LeanSphincsTest/Submission").glob("*.lean")]
        artifacts = freeze_artifacts(project, frozen, modules, "LeanSphincsTest.Submission")
        sandbox_config = json.loads((project / "sandbox.json").read_text())
        sandbox_config["verification_only"] = True
        (frozen / "sandbox.json").write_text(json.dumps(sandbox_config))
        (frozen / "comparator.json").write_text(json.dumps(config))
        frozen_env = env | {"HOME": str(frozen / "home"),
                            "COMPARATOR_LANDRUN": str(frozen / "strict-landrun.py")}
        command = systemd_command([str(lean / "bin/lake"), "env",
            str(COMPARATOR / ".lake/build/bin/comparator"), "comparator.json", "--verify-prebuilt"],
            frozen, frozen_env)
        log = directory / f"{case}.log"
        code = run(command, frozen, dict(os.environ), log)
        if artifacts != manifest(capture_artifacts(frozen, modules, "LeanSphincsTest.Submission")):
            raise RuntimeError("canary artifact snapshot drift")
        if (code == 0) != (case == "Good") or expected not in log.read_text():
            raise SystemExit(f"{case}: unexpected result; see {log}")
        print(f"sandboxed {case}: expected {'acceptance' if case == 'Good' else 'rejection'}", flush=True)
    print(f"Metric-only canaries passed; NOT a SchemeClaim baseline. Logs: {directory}")


if __name__ == "__main__":
    main()
