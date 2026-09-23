"""Fetch only a PR's bounded submission subtree at its frozen Git commit."""
from __future__ import annotations

import os
import re
import selectors
import signal
import subprocess
import tempfile
import time
from pathlib import Path

from check_submission import MAX_FILES, MAX_FILE_BYTES, MAX_TOTAL_BYTES

SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
MAX_TREE_OUTPUT = 4 * 1024 * 1024


class FetchError(ValueError):
    pass


def bounded(cmd: list[str], limit: int, timeout: int = 600) -> bytes:
    """Bound both captured output and the lifetime of the whole process group."""
    proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            start_new_session=True, bufsize=0)
    try:
        os.set_blocking(proc.stdout.fileno(), False)
        with selectors.DefaultSelector() as selector:
            selector.register(proc.stdout, selectors.EVENT_READ)
            output = bytearray()
            end = time.monotonic() + timeout
            while True:
                remaining = end - time.monotonic()
                if remaining <= 0:
                    raise FetchError("Git command timed out")
                if not selector.select(remaining):
                    continue
                try:
                    chunk = os.read(proc.stdout.fileno(), min(65536, limit - len(output) + 1))
                except BlockingIOError:
                    continue
                if not chunk:
                    break
                output.extend(chunk)
                if len(output) > limit:
                    raise FetchError("Git output exceeded its limit")
        proc.wait(timeout=max(0.1, end - time.monotonic()))
        if proc.returncode:
            raise FetchError(f"Git command failed: {bytes(output[-400:]).decode(errors='replace')}")
        return bytes(output)
    except subprocess.TimeoutExpired as exc:
        raise FetchError("Git command timed out") from exc
    finally:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.stdout.close()
        proc.wait()


def fetch_pr(repository: str, number: int, commit: str, destination: Path) -> str:
    """Resolve pull/N/head, verify its SHA, then batch-fetch admitted blobs."""
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repository):
        raise FetchError("invalid repository")
    if type(number) is not int or number < 1 or not SHA.fullmatch(commit):
        raise FetchError("invalid PR number or commit")
    if destination.exists():
        raise FetchError("destination must be new")
    with tempfile.TemporaryDirectory(prefix="sig-fetch-") as tmp:
        repo = Path(tmp) / "repo"
        bounded(["git", "init", "-q", str(repo)], 4096)
        remote = f"https://github.com/{repository}.git"
        bounded(["git", "-C", str(repo), "remote", "add", "origin", remote], 4096)
        bounded(["git", "-C", str(repo), "fetch", "-q", "--no-tags", "--filter=blob:none",
                 "--depth=1", "origin", f"refs/pull/{number}/head"], 4096)
        actual = bounded(["git", "-C", str(repo), "rev-parse", "FETCH_HEAD"], 4096).decode().strip()
        if actual != commit:
            raise FetchError("PR head changed during fetch")
        entries = bounded(["git", "-C", str(repo), "ls-tree", "-r", "-z", f"{commit}:submission"],
                          MAX_TREE_OUTPUT).split(b"\0")
        selected = []
        for entry in filter(None, entries):
            try:
                meta, raw_name = entry.split(b"\t", 1)
                mode, kind, oid = meta.split()
                name = raw_name.decode("utf-8", errors="strict")
            except (ValueError, UnicodeError) as exc:
                raise FetchError("invalid Git tree entry") from exc
            path = Path(name)
            if kind != b"blob" or mode not in (b"100644", b"100755") or not SHA.fullmatch(oid.decode()) or (
                path.is_absolute() or ".." in path.parts or not path.parts or path.parts[0] not in
                {"SigGolfCandidate", "Solution.lean", "claim.json"}):
                raise FetchError(f"invalid submission entry: {name!r}")
            selected.append((path, oid.decode()))
            if len(selected) > MAX_FILES:
                raise FetchError("submission has too many files")
        if not selected:
            raise FetchError("submission directory is empty")
        oids = list(dict.fromkeys(oid for _, oid in selected))
        # One request for all missing blobs avoids one network round trip per Lean module.
        bounded(["git", "-C", str(repo), "-c", "fetch.negotiationAlgorithm=noop", "fetch", "-q",
                 "--no-tags", "--no-write-fetch-head", "--recurse-submodules=no",
                 "origin", *oids], 4096)
        sizes = []
        for path, oid in selected:
            raw = bounded(["git", "-C", str(repo), "cat-file", "-s", oid], 64).strip()
            if not raw.isdigit():
                raise FetchError("Git reported an invalid blob size")
            size = int(raw)
            if size > MAX_FILE_BYTES:
                raise FetchError(f"{path}: file exceeds 8 MiB")
            sizes.append(size)
        if sum(sizes) > MAX_TOTAL_BYTES:
            raise FetchError("submission exceeds 16 MiB")
        destination.mkdir(parents=True)
        for (path, oid), size in zip(selected, sizes):
            output = destination / path
            output.parent.mkdir(parents=True, exist_ok=True)
            raw = bounded(["git", "-C", str(repo), "cat-file", "blob", oid], size)
            if len(raw) != size:
                raise FetchError("Git blob changed size")
            output.write_bytes(raw)
    return commit
