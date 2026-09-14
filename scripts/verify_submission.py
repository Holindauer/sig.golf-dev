#!/usr/bin/env python3
"""Isolated, content-addressed MVP verification. Reports are never promotions."""

import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

from artifact_snapshot import capture_artifacts, freeze_artifacts
from eligibility import deployment_gates, load_resource_profile
from benchmark_contract import metrics, render
from oracle_meter import meter_metadata
from scoring_policy import CLAIM_ID, load_scoring_profile, score_entry
from sandbox_profile import systemd_command
from source_bundle import capture, manifest, materialize
from worker_admission import WorkerBusy, worker_slot

ROOT = Path(__file__).resolve().parents[1]
COMPARATOR = ROOT / ".benchmark-tools/comparator"


@contextmanager
def termination_as_interrupt():
    """Give CLI SIGTERM the same worker cleanup path as Ctrl-C.

    Ignore repeated termination while unwinding so cleanup is not interrupted.
    SIGKILL and host failure remain outside this cooperative mechanism.
    Library callers retain control of their own process signal policy.
    """
    def terminate(signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt("SIGTERM")

    previous = signal.signal(signal.SIGTERM, terminate)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, previous)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_receipt(path: Path, report: dict) -> None:
    """Publish complete JSON only; a failed write must not look like a receipt.

    This is atomic publication, not an authenticated attestation. A hard kill
    before replacement may leave a temporary file, never a partial result.json.
    """
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    descriptor, temporary = tempfile.mkstemp(prefix=".receipt-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def check_integrity(project: Path, report: dict, tool_paths: dict[str, Path]) -> None:
    """Detect persistent input drift before scoring; not protection from a
    malicious same-user operator or a substitute for authenticated build caches.
    """
    if manifest(capture(project / "LeanSphincs/Submission")) != report["submission"]:
        raise RuntimeError("snapshot changed during verification; no score issued")
    if "artifacts" in report and manifest(capture_artifacts(project, report["artifact_modules"])) != report["artifacts"]:
        raise RuntimeError("artifact snapshot changed during verification")
    if harness_manifest() != report["harness"]:
        raise RuntimeError("harness changed during verification; no score issued")
    if check_dependencies() != report["dependencies"]:
        raise RuntimeError("dependencies changed during verification; no score issued")
    if {name: digest(path) for name, path in tool_paths.items()} != report["tools"]:
        raise RuntimeError("tool binaries changed during verification; no score issued")


def harness_manifest() -> dict:
    files = [ROOT / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                                      "LeanSphincs.lean", "benchmark.sh", "setup.sh")]
    for folder in ("scripts", "benchmark", "LeanSphincs/Benchmark"):
        files += [p for p in (ROOT / folder).iterdir()
                  if p.is_file() and p.name != "Challenge.lean"]
    return manifest({str(p.relative_to(ROOT)): p.read_bytes() for p in files})


def check_dependencies() -> dict:
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    revisions = {}
    for package in packages:
        path = ROOT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if package["type"] != "git" or revision != package["rev"]:
            raise RuntimeError(f"dependency pin mismatch: {package['name']}")
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain",
                                         "--untracked-files=no"], text=True)
        if dirty:
            raise RuntimeError(f"tracked dependency changes: {package['name']}")
        revisions[package["name"]] = revision
    return revisions


def prepare_project(project: Path, bundle: dict[str, bytes], source: str) -> None:
    project.mkdir()
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "LeanSphincs.lean"):
        shutil.copy2(ROOT / name, project / name)
    shutil.copytree(ROOT / "LeanSphincs/Benchmark", project / "LeanSphincs/Benchmark",
                    ignore=shutil.ignore_patterns("Challenge.lean"))
    materialize(bundle, project / "LeanSphincs/Submission")
    (project / "LeanSphincs/Benchmark/Challenge.lean").write_text(source)
    (project / ".lake").mkdir()
    (project / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
    # Only organizer artifacts: no shared writable cache or stale submission .oleans.
    if (ROOT / ".lake/config").exists():
        shutil.copytree(ROOT / ".lake/config", project / ".lake/config")
    for facet in ("lib/lean", "ir"):
        cached = ROOT / f".lake/build/{facet}/LeanSphincs/Benchmark"
        if cached.exists():
            shutil.copytree(cached, project / f".lake/build/{facet}/LeanSphincs/Benchmark",
                            ignore=shutil.ignore_patterns("Challenge.*"))
        (project / f".lake/build/{facet}/LeanSphincs/Submission").mkdir(parents=True)
    (project / "home").mkdir()
    shutil.copy2(ROOT / "benchmark/comparator.json", project / "comparator.json")
    for name in ("strict-landrun.py", "sandbox_profile.py", "check-axioms.lean"):
        shutil.copy2(ROOT / "scripts" / name, project / name)
    (project / "strict-landrun.py").chmod(0o700)


def run(command: list[str], project: Path, env: dict, log: Path, timeout: int = 4800) -> int:
    with log.open("wb") as output:
        process = subprocess.Popen(command, cwd=project, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                   start_new_session=True)
        try:
            return process.wait(timeout=timeout)
        finally:
            try:
                for unit in [arg.removeprefix("--unit=") for arg in command
                             if arg.startswith("--unit=leansphincs-")]:
                    stop_service(unit, output)
            finally:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()


def stop_service(unit, output):
    """A successful client exit alone does not establish descendant termination."""
    subprocess.run(["systemctl", "--user", "stop", unit], env=dict(os.environ),
                   stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT, timeout=15)
    state = subprocess.run(["systemctl", "--user", "show", unit,
        "--property=LoadState,ActiveState,ControlGroup"], env=dict(os.environ),
        capture_output=True, text=True, timeout=15)
    fields = dict(line.split("=", 1) for line in state.stdout.splitlines() if "=" in line)
    if not {"LoadState", "ActiveState", "ControlGroup"} <= fields.keys():
        raise RuntimeError("service cleanup uncertain: missing state for " + unit)
    if fields.get("LoadState") == "not-found":
        return  # systemd collected a terminated transient cgroup
    if state.returncode or fields.get("ActiveState") not in {"inactive", "failed"}:
        raise RuntimeError("service cleanup uncertain: " + unit)
    group = fields.get("ControlGroup")
    if group:
        events = Path("/sys/fs/cgroup") / group.lstrip("/") / "cgroup.events"
        try:
            if "populated 0" not in events.read_text().splitlines():
                raise RuntimeError("service descendants remain: " + unit)
        except FileNotFoundError:
            pass  # kernel has removed the stopped cgroup


def verify(submission: Path, insecure: bool = False) -> tuple[dict, Path]:
    result_root = ROOT / "benchmark-results/runs"
    result_root.mkdir(parents=True, exist_ok=True)
    try:
        with worker_slot(result_root):
            return _verify_admitted(submission, insecure)
    except WorkerBusy as error:
        now = int(time.time())
        report = {"schema": "leansphincs-verification-v2", "ranked": False,
                  "claim_version": CLAIM_ID,
                  "mathematical_verification": False, "resource_certification": False,
                  "side_channel_review": False, "deployment_eligible": False,
                  "hash_meter": meter_metadata(),
                  "profile": "insecure-local" if insecure else "leansphincs-linux-v1",
                  "status": "worker_busy", "stage": "admission", "retryable": True,
                  "started_unix": now, "finished_unix": now, "error": str(error), "logs": {}}
        directory = Path(tempfile.mkdtemp(prefix="run-", dir=result_root))
        os.chmod(directory, 0o700)
        write_receipt(directory / "result.json", report)
        return report, directory


def _verify_admitted(submission: Path, insecure: bool = False) -> tuple[dict, Path]:
    result_root = ROOT / "benchmark-results/runs"
    result_root.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="run-", dir=result_root))
    os.chmod(directory, 0o700)
    report = {"schema": "leansphincs-verification-v2", "ranked": False,
              "claim_version": CLAIM_ID,
              "mathematical_verification": False, "resource_certification": False,
              "side_channel_review": False, "deployment_eligible": False,
              "hash_meter": meter_metadata(),
              "profile": "insecure-local" if insecure else "leansphincs-linux-v1",
              "status": "infrastructure_error", "started_unix": int(time.time())}
    stage = "capture"
    try:
        bundle = capture(submission)
        report["submission"] = manifest(bundle)
        stage = "source_policy"
        materialize(bundle, directory / "source")
        sigma, hverify, bound = metrics(directory / "source")
        check = subprocess.run(["bash", str(ROOT / "scripts/check-submission-imports.sh"),
                                str(directory / "source")], capture_output=True, text=True)
        if check.returncode:
            raise ValueError(check.stderr.strip() or check.stdout.strip())
        report["metrics"] = {"sigma": sigma, "hverify": hverify, "bound": bound}
        stage = "setup"
        report["harness"] = harness_manifest()
        report["resource_profile"] = load_resource_profile(ROOT / "benchmark/resources.json")
        report["deployment_gates"] = deployment_gates(report["resource_profile"])
        report["scoring_profile"] = load_scoring_profile(ROOT / "benchmark/scoring.json")
        report["dependencies"] = check_dependencies()
        lean = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
        tool_paths = {"comparator": COMPARATOR / ".lake/build/bin/comparator",
                     "exporter": COMPARATOR / ".lake/packages/lean4export/.lake/build/bin/lean4export",
                     "lean": lean / "bin/lean", "lake": lean / "bin/lake",
                     "leanchecker": lean / "bin/leanchecker"}
        landrun = ROOT / ".benchmark-tools/landrun/landrun"
        if not insecure:
            tool_paths["landrun"] = landrun
        report["tools"] = {name: digest(path) for name, path in tool_paths.items()}
        if not insecure:
            stage = "sandbox_preflight"
            spec = importlib.util.spec_from_file_location("check_sandbox", ROOT / "scripts/check-sandbox.py")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            report["sandbox"] = module.check(lean, tool_paths["exporter"], landrun)
        stage = "trusted_build"
        project = directory / "project"
        prepare_project(project, bundle, render(sigma, hverify, bound))
        (project / "sandbox.json").write_text(json.dumps({"lean_prefix": str(lean),
            "exporter": str(tool_paths["exporter"]), "landrun": str(landrun)}))
        env = {"PATH": f"{lean}/bin:/usr/bin:/bin", "HOME": str(project / "home"),
               "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1"}
        # Challenge imports protected definitions only, never candidate code.
        if run([str(lean / "bin/lake"), "build", "LeanSphincs.Benchmark.Challenge", "LeanSphincs"],
               project, env, directory / "trusted-build.log"):
            raise RuntimeError("trusted template build failed; see trusted-build.log")
        if run([str(lean / "bin/lake"), "env", "lean", "check-axioms.lean"], project,
               env, directory / "axioms.log"):
            raise RuntimeError("protected axiom audit failed; see axioms.log")
        env.update(COMPARATOR_LEAN4EXPORT=str(tool_paths["exporter"]),
                   COMPARATOR_LANDRUN=str(COMPARATOR / "scripts/fake-landrun.sh") if insecure
                   else str(project / "strict-landrun.py"))
        stage = "compilation"
        compile_command = [str(lean / "bin/lake"), "build", "LeanSphincs.Submission.Solution"]
        if not insecure:
            compile_command = [str(project / "strict-landrun.py"), "--"] + compile_command
            compile_command = systemd_command(compile_command, project, env)
        code = run(compile_command, project, env if insecure else dict(os.environ), directory / "compile.log")
        report["compilation_exit"] = code
        if code:
            report["status"] = "verification_failed"
        else:
            stage = "artifact_capture"
            frozen = directory / "verification"
            prepare_project(frozen, bundle, render(sigma, hverify, bound))
            # Only trusted outputs are copied from the build project outside the
            # candidate write grants. Never copy its configuration or IR.
            for name in ("Benchmark",):
                shutil.copytree(project / ".lake/build/lib/lean/LeanSphincs" / name,
                                frozen / ".lake/build/lib/lean/LeanSphincs" / name, dirs_exist_ok=True)
            report["artifact_modules"] = sorted(Path(n).stem for n in bundle if n.endswith(".lean"))
            report["artifacts"] = freeze_artifacts(project, frozen, report["artifact_modules"])
            (frozen / "sandbox.json").write_text(json.dumps({"lean_prefix": str(lean),
                "exporter": str(tool_paths["exporter"]), "landrun": str(landrun), "verification_only": True}))
            project = frozen
            env["HOME"] = str(project / "home")
            if not insecure:
                env["COMPARATOR_LANDRUN"] = str(project / "strict-landrun.py")
            stage = "comparison"
            command = [str(lean / "bin/lake"), "env", str(tool_paths["comparator"]),
                       "comparator.json", "--verify-prebuilt"]
            if not insecure:
                command = systemd_command(command, project, env)
            code = run(command, project, env if insecure else dict(os.environ), directory / "comparator.log")
        report["comparator_exit"] = code
        stage = "integrity"
        check_integrity(project, report, tool_paths)
        report["status"] = "accepted" if code == 0 else "verification_failed"
        if code == 0:
            report["mathematical_verification"] = True
            score = score_entry(report["scoring_profile"], sigma, hverify)
            if score is None:
                report["score_pending"] = "bandwidth coefficient not calibrated"
            else:
                report["score"] = score
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        report.pop("score", None)
        report["status"] = "source_rejected" if stage in {"capture", "source_policy"} else "infrastructure_error"
        report["error"] = str(error)
    except KeyboardInterrupt:
        report.pop("score", None)
        report["status"] = "interrupted"
        report["error"] = "verification interrupted; worker stop requested"
    if "resource_profile" in report:
        report["deployment_gates"] = deployment_gates(report["resource_profile"], report)
    report["stage"] = stage
    report["finished_unix"] = int(time.time())
    report["logs"] = {p.name: digest(p) for p in directory.glob("*.log")}
    write_receipt(directory / "result.json", report)
    return report, directory


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("submission", nargs="?", type=Path, default=ROOT / "LeanSphincs/Submission")
    parser.add_argument("--insecure-local", action="store_true", help="organizer-owned diagnostics only")
    args = parser.parse_args()
    with termination_as_interrupt():
        report, directory = verify(args.submission, args.insecure_local)
    print(json.dumps({"status": report["status"], "ranked": False, "result": str(directory / "result.json"),
                      **({"error": report["error"]} if "error" in report else {})}))
    sys.exit(0 if report["status"] == "accepted" else 1)
