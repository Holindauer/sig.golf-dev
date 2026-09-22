#!/usr/bin/env python3
"""Pin or check the protected files of the contract.

    pin_contract.py pin   [--root DIR]   # (re)write verifier/protected.sha256
    pin_contract.py check [--root DIR]   # exit 0 iff every protected file matches the pin
    pin_contract.py id    [--root DIR]   # print the contract id (sha256 of the pin file)

The protected list lives in challenges.json; the pin file it names holds one sha256 per protected
file. The contract id is the sha256 of the pin file: together with the version name it identifies
exactly which statement, limits and verifier every score refers to. Standard library only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


class ContractError(Exception):
    pass


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def load_challenges(root: Path) -> dict:
    try:
        return json.loads((root / "challenges.json").read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ContractError(f"cannot read challenges.json: {exc}") from exc


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def digest_lines(root: Path, cfg: dict) -> list[str]:
    lines = []
    for rel in sorted(cfg["protected"]):
        path = root / rel
        if not path.is_file():
            raise ContractError(f"protected file missing: {rel}")
        lines.append(f"{sha256_file(path)}  {rel}")
    return lines


def pin_path(root: Path, cfg: dict) -> Path:
    return root / cfg["contract"]["pin_file"]


def contract_id(root: Path) -> str:
    """The sha256 of the pin file as it is in the checkout."""
    cfg = load_challenges(root)
    pin = pin_path(root, cfg)
    if not pin.is_file():
        raise ContractError(f"pin file missing: {pin}")
    return hashlib.sha256(pin.read_bytes()).hexdigest()


def mismatches(root: Path) -> list[str]:
    """The protected files whose digest differs from the pin, or that the pin does not list."""
    cfg = load_challenges(root)
    pin = pin_path(root, cfg)
    if not pin.is_file():
        raise ContractError(f"pin file missing: {pin}")
    content = pin.read_text(encoding="utf-8")
    expected = dict(line.split("  ", 1)[::-1] for line in content.splitlines() if line.strip())
    actual = dict(line.split("  ", 1)[::-1] for line in digest_lines(root, cfg))
    return [rel for rel in sorted(set(expected) | set(actual)) if expected.get(rel) != actual.get(rel)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["pin", "check", "id"])
    ap.add_argument("--root", type=Path)
    a = ap.parse_args()
    root = (a.root or repo_root()).resolve()
    try:
        cfg = load_challenges(root)
        if a.cmd == "pin":
            content = "\n".join(digest_lines(root, cfg)) + "\n"
            pin_path(root, cfg).write_text(content, encoding="utf-8")
            print(f"pinned {len(cfg['protected'])} files; contract id {hashlib.sha256(content.encode()).hexdigest()}")
            return 0
        if a.cmd == "id":
            print(contract_id(root))
            return 0
        bad = mismatches(root)
        for rel in bad:
            print(f"protected file differs from the pin: {rel}", file=sys.stderr)
        if not bad:
            print(f"contract ok: {cfg['contract']['version']} {contract_id(root)[:16]}")
        return 0 if not bad else 1
    except ContractError as exc:
        print(f"pin_contract: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
