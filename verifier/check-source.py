#!/usr/bin/env python3
"""Enforce the flat source policy before parsing or compiling a submission."""

from pathlib import Path
import sys
from source_bundle import capture


def check(root: Path) -> None:
    try:
        capture(root)
    except OSError as error:
        raise ValueError(f"invalid source bundle: {error}") from error


if __name__ == "__main__":
    try:
        if len(sys.argv) != 2:
            raise ValueError("usage: check-source.py SUBMISSION_DIR")
        check(Path(sys.argv[1]))
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
