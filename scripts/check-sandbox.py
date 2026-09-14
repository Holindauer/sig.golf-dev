#!/usr/bin/env python3
"""Exercise mandatory filesystem/network boundaries before accepting a job."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from sandbox_profile import landlock_abi, landrun_args, systemd_command, PROFILE

ROOT = Path(__file__).resolve().parents[1]


def check(lean: Path, exporter: Path, landrun: Path) -> dict:
    abi = landlock_abi()
    with tempfile.TemporaryDirectory(prefix="leansphincs-probe-") as name:
        parent = Path(name)
        root = parent / "job"
        for sub in (".lake/build/lib/lean/LeanSphincs/Submission", ".lake/build/ir/LeanSphincs/Submission",
                    ".lake/packages", ".lake/config", ".lake/build/lib/lean/LeanSphincs/Benchmark",
                    "LeanSphincs/Submission", "home"):
            (root / sub).mkdir(parents=True, exist_ok=True)
        (parent / "unreadable.txt").write_text("synthetic private marker")
        dependency = parent / "dependency"
        dependency.mkdir()
        (dependency / "readonly.txt").write_text("dependency")
        (root / ".lake/packages/probe").symlink_to(dependency, target_is_directory=True)
        (root / "protected.txt").write_text("protected")
        (root / ".lake/config/protected.olean").write_text("protected")
        (root / ".lake/build/lib/lean/LeanSphincs/Benchmark/protected.olean").write_text("protected")
        (root / "LeanSphincs/Submission/Scheme.lean").write_text("protected")
        shutil.copy2(ROOT / "scripts/sandbox-probe.py", root / "probe.py")
        reports = {}
        for mode in ("compile", "verify"):
            command = landrun_args(landrun, root, lean, exporter,
                ["/usr/bin/python3", str(root / "probe.py"), str(parent / "unreadable.txt"), mode],
                build=mode == "compile")
            env = {"PATH": f"{lean}/bin:/usr/bin:/bin", "HOME": str(root / "home"), "LANG": "C.UTF-8"}
            from verify_submission import run
            log = parent / (mode + ".log")
            code = run(systemd_command(command, root, env, runtime_seconds=30),
                       root, dict(os.environ), log, timeout=60)
            if code:
                raise RuntimeError("sandbox probe failed; refusing untrusted compilation:\n" + log.read_text())
            # Cleanup diagnostics can follow the probe's JSON line.
            report = json.loads(log.read_text().splitlines()[0])
            if report.get("probe") != "passed":
                raise RuntimeError("sandbox probe did not confirm enforcement")
            reports[mode] = report

        return {"profile": PROFILE, "landlock_abi": abi, "phases": reports, **reports["compile"]}


if __name__ == "__main__":
    lean = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    report = check(lean,
        ROOT / ".benchmark-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export",
        ROOT / ".benchmark-tools/landrun/landrun")
    print(json.dumps(report, sort_keys=True))
