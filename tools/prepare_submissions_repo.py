#!/usr/bin/env python3
"""Prepare an empty local submissions repository pinned to this committed core checkout.

    python3 tools/prepare_submissions_repo.py /path/to/sig.golf-submissions

Creates a new directory, stages its initial contents (README, AGENTS, pull-request template, an
empty records.json registry and the `.contract` submodule; no submission roots), and configures its
GitHub remote. Uses a local clone for the contract submodule; it never pushes or contacts GitHub.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CORE_URL = "https://github.com/leanEthereum/sig.golf-dev.git"
SUBMISSIONS_URL = "https://github.com/leanEthereum/sig.golf-submissions.git"
TEMPLATE = "tools/submissions_template"
EMPTY_REGISTRY = {"version": 1, "records": {}}


def git(root: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True, text=True)
    return result.stdout.strip()


def blob(root: Path, commit: str, path: str) -> bytes:
    return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"],
                          check=True, capture_output=True).stdout


def tracked_files(root: Path, commit: str, prefix: str) -> list[str]:
    return git(root, "ls-tree", "-r", "--name-only", commit, "--", prefix + "/").splitlines()


def prepare(root: Path, destination: Path) -> dict:
    root, destination = root.resolve(), destination.resolve()
    if destination.exists():
        raise ValueError("destination must be a new directory; existing submissions are never overwritten")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("commit the core changes before preparing the submissions repository")
    commit = git(root, "rev-parse", "HEAD")
    config = json.loads(blob(root, commit, "challenges.json"))
    pin = hashlib.sha256(blob(root, commit, config["contract"]["pin_file"])).hexdigest()
    tracks = list(config["tracks"])

    destination.mkdir(parents=True)
    git(destination, "init", "--initial-branch=main")
    git(destination, "remote", "add", "origin", SUBMISSIONS_URL)
    if git(root, "ls-tree", "--name-only", commit, "--", "LICENSE") == "LICENSE":
        (destination / "LICENSE").write_bytes(blob(root, commit, "LICENSE"))
    for name in tracked_files(root, commit, TEMPLATE):
        path = destination / Path(name).relative_to(TEMPLATE)
        path.parent.mkdir(parents=True, exist_ok=True)
        content = blob(root, commit, name).decode()
        path.write_text(content.replace("{{CONTRACT_COMMIT}}", commit).replace("{{CONTRACT_ID}}", pin))
    (destination / "records.json").write_text(json.dumps(EMPTY_REGISTRY, indent=2) + "\n")

    git(destination, "-c", "protocol.file.allow=always", "submodule", "add", "--name", "contract",
        "--", str(root), ".contract")
    git(destination / ".contract", "checkout", "--detach", commit)
    git(destination / ".contract", "remote", "set-url", "origin", CORE_URL)
    git(destination, "config", "--file", ".gitmodules", "submodule.contract.url", CORE_URL)
    git(destination, "config", "submodule.contract.url", CORE_URL)
    git(destination, "add", "--all")
    return {"directory": str(destination), "core_commit": commit, "contract_id": pin,
            "tracks": [t["slug"] for t in tracks]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    try:
        subprocess.run([sys.executable, str(ROOT / "verifier/pin_contract.py"), "check"], check=True)
        result = prepare(ROOT, args.destination)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(f"Cannot prepare submissions repository: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    print("Initial files are staged locally. Review and commit them before publishing both repositories.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
