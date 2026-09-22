"""Shared fixtures: an open track, a fixed contract fingerprint and a sigma/hverify vocabulary."""
from __future__ import annotations

import copy
import json
from unittest.mock import patch

from app import contract

EPOCH = "e" * 64
ROOT = "formal/Submissions/Full"
REQUIRED = ("Scheme.lean", "Solution.lean", "sigma.txt", "hverify.txt", "bound.txt")


def open_config() -> dict:
    cfg = copy.deepcopy(contract.load())
    for t in cfg["tracks"]:
        t["admission"] = "open"
    return cfg


def pin_contract(test, epoch: str = EPOCH) -> None:
    """Fix the contract fingerprint: the worktree may lack the pin the verifier generates."""
    change = patch("app.contract.contract_id", return_value=epoch)
    change.start()
    test.addCleanup(change.stop)


def open_admission(test) -> None:
    change = patch.object(contract, "load", return_value=open_config())
    change.start()
    test.addCleanup(change.stop)


def write_root(folder, *, sigma=2274, hverify=160, notes="## Idea\n\nA fixture.\n") -> None:
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "Scheme.lean").write_text("-- scheme fixture\n")
    (folder / "Solution.lean").write_text("-- solution fixture\n")
    (folder / "sigma.txt").write_text(f"{sigma}\n")
    (folder / "hverify.txt").write_text(f"{hverify}\n")
    (folder / "bound.txt").write_text(json.dumps([[4, 1, 1, 0, 128]]) + "\n")
    if notes is not None:
        (folder / "NOTES.md").write_text(notes)
