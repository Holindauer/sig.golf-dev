#!/usr/bin/env python3
"""Verify one submission the way the hosted sig.golf verifier does.

    verify.py TRACK --source URL_OR_DIR [--commit SHA] [--work DIR] [--keep] [--json]
                    [--hide DIR]... [--archive-dir DIR --archive-id ID] [--insecure-local]

Pipeline
  0. Check the trusted checkout against its contract pin (challenges.json contract.pin_file).
     A mismatch is an infrastructure failure: nothing of the candidate is processed.
  1. Export the track's submission root, and nothing else, from `--source` at `--commit`
     (or from the working tree of a local `--source` when no commit is given). Only flat,
     bounded regular files are copied; blobs are read directly, never checked out. With
     `--archive-dir`, the exact root is retained as a durable ZIP before any candidate code
     runs, or restored from that store when it already holds this submission.
  2. Hand that directory to verifier/verify_submission.py, the isolated verifier, which captures,
     policy-checks, compiles in its sandbox and compares against the protected statement.
  3. Translate its receipt into the service result:
     verified | rejected | policy_rejected | timeout | failed.

`--hide` is accepted for compatibility with the hosting worker. This verifier's sandbox is an
allowlist (Landlock through landrun plus a transient systemd service): the candidate only sees
the private project, the pinned toolchain and the read-only dependency packages, so directories
named here are inaccessible whether or not they are listed. They are recorded in the log.

The result never promotes anything: receipts say ranked: false, and the site decides records
after the verdict is durable on GitHub.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent          # verifier/
ROOT = HERE.parent                              # the repository: challenges.json, formal/, verifier/
sys.path.insert(0, str(HERE))
from source_archive import ArchiveError, read_metadata, restore_source, save_source  # noqa: E402

SHA_RE = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
LOG_CAP = 4 * 1024 * 1024
NOTES_CAP = 64 * 1024
VERIFIED = "verified"
_CHILDREN: set[subprocess.Popen] = set()


class Reject(Exception):
    """The submission is refused before anything of it reaches the verifier."""


class Failure(Exception):
    """Ours, not theirs: the pipeline could not reach a verdict."""


def load_challenges(root: Path = ROOT) -> dict:
    return json.loads((root / "challenges.json").read_text(encoding="utf-8"))


def track(cfg: dict, slug: str) -> dict:
    for entry in cfg["tracks"]:
        if entry["slug"] == slug:
            return entry
    raise Failure(f"unknown track {slug!r}")


def contract_id(cfg: dict, root: Path = ROOT) -> str:
    pin = root / cfg["contract"]["pin_file"]
    if not pin.is_file():
        raise Failure(f"contract pin missing: {pin}")
    return hashlib.sha256(pin.read_bytes()).hexdigest()


def check_pin(root: Path = ROOT) -> None:
    """Fail closed if any protected file of the trusted checkout differs from its pin."""
    proc = subprocess.run([sys.executable, str(HERE / "pin_contract.py"), "check", "--root", str(root)],
                          capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if proc.returncode:
        raise Failure("protected files differ from the contract pin: " + (proc.stderr or proc.stdout).strip())


def bounded_output(cmd: list[str], limit: int, timeout: int = 120, cwd: Path | None = None) -> bytes:
    """Read untrusted git output with a byte cap and a whole-process-group kill on overflow."""
    proc = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL, start_new_session=True)
    _CHILDREN.add(proc)
    chunks: list[bytes] = []
    exceeded = False

    def read():
        nonlocal exceeded
        size = 0
        for chunk in iter(lambda: proc.stdout.read(65536), b""):
            size += len(chunk)
            if size > limit:
                exceeded = True
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                return
            chunks.append(chunk)

    reader = threading.Thread(target=read, daemon=True)
    reader.start()
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
        raise Failure(f"git timed out: {' '.join(cmd[:3])}")
    finally:
        reader.join(5)
        proc.stdout.close()
        _CHILDREN.discard(proc)
    if exceeded:
        raise Reject("submission metadata or file exceeds its size limit")
    data = b"".join(chunks)
    if proc.returncode:
        raise Failure(f"{' '.join(cmd[:3])} failed: {data.decode(errors='replace')[-800:]}")
    return data


def _check_sizes(entries: list[tuple[str, int]], rel_root: str, limits: dict) -> None:
    if not entries:
        raise Reject(f"the commit has no files in {rel_root}")
    if len(entries) > limits["max_files"]:
        raise Reject(f"more than {limits['max_files']} files in {rel_root}")
    if any(size > limits["max_file_bytes"] for _, size in entries):
        raise Reject(f"a file in {rel_root} exceeds {limits['max_file_bytes']} bytes")
    if sum(size for _, size in entries) > limits["max_total_bytes"]:
        raise Reject(f"{rel_root} exceeds {limits['max_total_bytes']} bytes in total")
    for name, _ in entries:
        if "/" in name or name in {".", ".."} or name.startswith("."):
            raise Reject(f"{name!r}: hidden files and nested paths are not admitted")


def export_root(source: str, commit: str | None, rel_root: str, dest: Path, limits: dict) -> str:
    """Copy only flat, bounded regular files of the submission root into `dest`.

    Returns the full commit hash, or "worktree" for a local uncommitted tree. Filenames are
    admitted here by shape only; verify_submission.py applies the source policy to the copy.
    """
    dest.mkdir(parents=True, exist_ok=False)
    if commit is None:
        src = Path(source) / rel_root
        if src.is_symlink() or not src.is_dir():
            raise Reject(f"{source} has no regular directory {rel_root}")
        entries = []
        for path in sorted(src.iterdir()):
            info = path.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise Reject(f"{path.name!r}: only regular files are admitted")
            entries.append((path.name, info.st_size))
        _check_sizes(entries, rel_root, limits)
        for name, _ in entries:
            fd = os.open(src / name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(fd, "rb") as stream:
                data = stream.read(limits["max_file_bytes"] + 1)
            if len(data) > limits["max_file_bytes"]:
                raise Reject(f"{name!r} grew beyond its size limit while being copied")
            (dest / name).write_bytes(data)
        return "worktree"
    if not commit or commit.startswith("-") or "\x00" in commit or not re.fullmatch(r"[0-9a-fA-F]{7,64}", commit):
        raise Reject("invalid commit revision")
    with tempfile.TemporaryDirectory(prefix="sig-src-", dir=dest.parent) as tmp:
        if Path(source).is_dir():
            repo = Path(source)
        else:
            repo = Path(tmp) / "repo"
            bounded_output(["git", "init", "--quiet", str(repo)], LOG_CAP)
            bounded_output(["git", "-C", str(repo), "remote", "add", "origin", "--", source], LOG_CAP)
            bounded_output(["git", "-C", str(repo), "fetch", "--quiet", "--filter=blob:none", "--depth=1",
                            "--", "origin", commit], LOG_CAP, timeout=600)
        full = bounded_output(["git", "-C", str(repo), "rev-parse", "--verify", "--end-of-options",
                               f"{commit}^{{commit}}"], 4096).decode().strip()
        if not SHA_RE.fullmatch(full):
            raise Failure("git did not resolve a canonical commit hash")
        tree = bounded_output(["git", "-C", str(repo), "ls-tree", "-l", "-z", f"{full}:{rel_root}"],
                              limits["max_files"] * 4096)
        blobs = []
        for entry in filter(None, tree.split(b"\0")):
            meta, raw_name = entry.split(b"\t", 1)
            mode, kind, oid, size = meta.split()
            name = raw_name.decode("utf-8", errors="replace")
            if kind != b"blob" or mode not in (b"100644", b"100755"):
                raise Reject(f"{name!r}: only regular files are admitted (no directories or symlinks)")
            blobs.append((name, int(size), oid.decode("ascii")))
        _check_sizes([(n, s) for n, s, _ in blobs], rel_root, limits)
        for name, size, oid in blobs:
            data = bounded_output(["git", "-C", str(repo), "cat-file", "blob", oid], size)
            if len(data) != size:
                raise Failure("git blob size changed unexpectedly")
            (dest / name).write_bytes(data)
        return full


def read_notes(staged: Path) -> str | None:
    """The submitter's NOTES.md, published whatever the verdict; untrusted text, capped."""
    path = staged / "NOTES.md"
    if path.is_symlink() or not path.is_file():
        return None
    return path.read_bytes()[:NOTES_CAP].decode("utf-8", errors="replace")


def run_verifier(staged: Path, insecure: bool, log: Path) -> tuple[dict, Path]:
    """Run the isolated verifier as its own process and return its CLI summary and run directory."""
    cmd = [sys.executable, str(HERE / "verify_submission.py"), str(staged)]
    if insecure:
        cmd.append("--insecure-local")
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            stdin=subprocess.DEVNULL, start_new_session=True)
    _CHILDREN.add(proc)
    try:
        stdout, stderr = proc.communicate()
    finally:
        _CHILDREN.discard(proc)
    with log.open("a", encoding="utf-8") as out:
        out.write(stderr[-LOG_CAP:])
    summary = None
    for line in reversed(stdout.strip().splitlines()):
        try:
            candidate = json.loads(line)
        except ValueError:
            continue
        if isinstance(candidate, dict) and "status" in candidate:
            summary = candidate
            break
    if summary is None or not isinstance(summary.get("result"), str):
        raise Failure(f"verify_submission.py exited {proc.returncode} without a receipt: {stderr[-600:]}")
    receipt = Path(summary["result"])
    if not receipt.is_file():
        raise Failure("verify_submission.py reported a receipt that does not exist")
    return summary, receipt.parent


def _tail(path: Path, n: int = 2000) -> str:
    try:
        return path.read_text(errors="replace")[-n:]
    except OSError:
        return ""


def interpret(report: dict, slug: str, commit: str, limits: dict, run_dir: Path | None = None) -> dict:
    """Map a verify_submission receipt onto the service's result vocabulary.

    accepted -> verified; verification_failed -> rejected; source_rejected -> policy_rejected;
    timed_out -> timeout; worker_busy, interrupted and infrastructure_error -> failed.
    """
    status = report.get("status")
    result = {"track": slug, "commit": commit, "claim_version": report.get("claim_version"),
              "hash_meter": (report.get("hash_meter") or {}).get("id") if isinstance(report.get("hash_meter"), dict)
              else report.get("hash_meter"),
              "comparator_exit": report.get("comparator_exit"), "compilation_exit": report.get("compilation_exit"),
              "ranked": False}
    metrics = report.get("metrics") or {}
    error = report.get("error") or ""
    if status == "accepted":
        sigma, hverify = metrics.get("sigma"), metrics.get("hverify")
        score = (report.get("score") or {}).get("value")
        if (type(sigma) is not int or type(hverify) is not int or sigma <= 0 or hverify <= 0
                or sigma > limits["max_metric"] or hverify > limits["max_metric"]
                or score != str(sigma * hverify)):
            raise Failure("accepted receipt carries inconsistent metrics")
        result.update(status=VERIFIED, sigma=sigma, hverify=hverify, score=score, bound=metrics.get("bound"),
                      objective="sigma * hverify")
    elif status == "verification_failed":
        tail = ""
        if run_dir is not None:
            log = "compile.log" if report.get("compilation_exit") else "comparator.log"
            tail = _tail(run_dir / log)
        if error:
            reason = error
        elif report.get("compilation_exit"):
            reason = "the submission did not compile against the protected statement"
        else:
            reason = "the comparator rejected the exported theorem"
        result.update(status="rejected", reason=reason[-2000:], tail=tail[-2000:])
    elif status == "source_rejected":
        result.update(status="policy_rejected", errors=[error[-2000:] or status])
    elif status == "timed_out":
        result.update(status="timeout", limit_s=report.get("limit_seconds"),
                      reason=error[-2000:] or "the verification exceeded its wall-clock budget")
    elif status == "worker_busy":
        result.update(status="failed", reason="another verification owns this checkout; retry later", retryable=True)
    elif status == "interrupted":
        result.update(status="failed", reason="verification was interrupted", retryable=True)
    else:
        result.update(status="failed", reason=(error or f"verifier status {status!r}")[-2000:], retryable=False)
    return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("track")
    ap.add_argument("--source", required=True, help="git URL, or a local directory (git repo or plain tree)")
    ap.add_argument("--commit", help="commit to verify; omit to take the working tree of a local --source")
    ap.add_argument("--work", type=Path, help="work directory (default: a temp dir)")
    ap.add_argument("--hide", type=Path, action="append", default=[],
                    help="directories the proof must not see; this sandbox is an allowlist, so they "
                         "are inaccessible regardless and only recorded")
    ap.add_argument("--archive-dir", type=Path, help="durable source store, outside disposable work")
    ap.add_argument("--archive-id", help="32-digit submission id; required with --archive-dir")
    ap.add_argument("--keep", action="store_true", help="keep the work directory")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--insecure-local", action="store_true",
                    help="organizer diagnostics only: run the verifier without its Linux sandbox")
    a = ap.parse_args()
    if bool(a.archive_dir) != bool(a.archive_id) or (a.archive_dir and not a.commit):
        ap.error("--archive-dir and --archive-id require each other and an exact --commit")

    cfg = load_challenges()
    limits = cfg["limits"]
    work = (a.work or Path(tempfile.mkdtemp(prefix="sig-verify-"))).absolute()
    if a.archive_dir:
        a.archive_dir = a.archive_dir.resolve()
        if a.archive_dir.is_relative_to(work.resolve()) or work.resolve().is_relative_to(a.archive_dir):
            ap.error("source archive storage must be separate from disposable work")
    if a.work:
        # This directory is removed after successful runs; never adopt an existing path.
        try:
            work.mkdir(mode=0o700, parents=True, exist_ok=False)
        except OSError as exc:
            ap.error(f"--work must be a new directory: {exc}")
    log_path = work / "verify.log"
    log_path.touch()
    t0 = time.monotonic()
    result = {"track": a.track, "source": a.source, "status": "failed", "work": str(work), "ranked": False}

    def stop(signum, _frame):
        for child in tuple(_CHILDREN):
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        raise SystemExit(128 + signum)

    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, stop)

    def finish(**extra) -> int:
        result.update(duration_s=round(time.monotonic() - t0, 1),
                      finished_at=datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
                      log=str(log_path), **extra)
        if a.json:
            print(json.dumps(result, indent=2, sort_keys=True))
        else:
            print(f"{result['status']}: track={a.track} commit={result.get('commit')} "
                  f"score={result.get('score')} in {result['duration_s']}s (log: {log_path})")
        if not a.keep and result["status"] in {VERIFIED, "rejected", "policy_rejected", "timeout"}:
            shutil.rmtree(work, ignore_errors=True)
        return 0 if result["status"] == VERIFIED else 1

    try:
        # 0. the trusted checkout first: nothing of the candidate is read before the pin holds
        check_pin()
        result["contract"] = contract_id(cfg)
        t = track(cfg, a.track)
        if a.hide:
            with log_path.open("a", encoding="utf-8") as out:
                out.write("hidden from the proof (allowlisted sandbox): " +
                          ", ".join(str(d) for d in a.hide) + "\n")
        # 1. the submission root only
        staged = work / "staged"
        retained = read_metadata(a.archive_dir, a.archive_id) if a.archive_dir else None
        if retained is not None:
            result["commit"] = restore_source(a.archive_dir, retained, staged, commit=a.commit, track=a.track,
                                               contract=result["contract"], submission_root=t["submission_root"])
            result["source_archive"] = retained
        else:
            result["commit"] = export_root(a.source, a.commit, t["submission_root"], staged, limits)
            if a.archive_dir:
                if result["commit"] != a.commit:
                    raise ArchiveError("archive retention requires the exact resolved commit")
                # The trusted parent publishes durable bytes before any candidate code executes.
                result["source_archive"] = save_source(a.archive_dir, a.archive_id, staged,
                    source_repo=a.source, commit=result["commit"], track=a.track,
                    submission_root=t["submission_root"], contract=result["contract"])
        notes = read_notes(staged)
        if notes:
            result["notes"] = notes
        # 2. the isolated verifier
        summary, run_dir = run_verifier(staged, a.insecure_local, log_path)
        report = json.loads((run_dir / "result.json").read_text(encoding="utf-8"))
        with log_path.open("a", encoding="utf-8") as out:
            for name in ("trusted-build.log", "axioms.log", "compile.log", "comparator.log"):
                path = run_dir / name
                if path.is_file():
                    out.write(f"\n===== {name} =====\n{_tail(path, LOG_CAP)}")
        # 3. the verdict
        verdict = interpret(report, a.track, result["commit"], limits, run_dir)
        verdict["receipt"] = str(run_dir / "result.json")
        return finish(**verdict)
    except Reject as exc:
        with log_path.open("a", encoding="utf-8") as out:
            out.write(str(exc) + "\n")
        return finish(status="policy_rejected", errors=[str(exc)])
    except (ArchiveError, Failure, OSError, ValueError, subprocess.SubprocessError) as exc:
        with log_path.open("a", encoding="utf-8") as out:
            out.write(str(exc) + "\n")
        return finish(status="failed", reason=str(exc)[-2000:], retryable=False)


if __name__ == "__main__":
    raise SystemExit(main())
