#!/usr/bin/env python3
"""Render sigma.txt, hverify.txt and bound.txt into the trusted theorem template."""

from pathlib import Path
import json
import sys
from benchmark_contract import metrics, render


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: render-benchmark-challenge.py SUBMISSION_DIR OUTPUT [SNAPSHOT]")
    try:
        sigma, hverify, bound = metrics(Path(sys.argv[1]))
        source = render(sigma, hverify, bound)
        output = Path(sys.argv[2])
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(source, encoding="utf-8")
        if len(sys.argv) == 4:
            Path(sys.argv[3]).write_text(json.dumps({
                "sigma": sigma, "hverify": hverify, "bound": bound,
            }) + "\n", encoding="utf-8")
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
