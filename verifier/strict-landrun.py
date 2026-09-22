#!/usr/bin/env python3
"""Comparator adapter: replace inherited broad grants with the pinned profile.

The comparator invokes this trusted script outside its child sandbox. Incoming
landrun flags are never authority; only the command after -- is considered.
"""

import json
import os
from pathlib import Path
import sys
from sandbox_profile import landrun_args


def main():
    root = Path.cwd().resolve()
    config = json.loads((root / "sandbox.json").read_text())
    args = sys.argv[1:]
    if "--" not in args:
        raise ValueError("missing command delimiter")
    command = args[args.index("--") + 1:]
    lean = Path(config["lean_prefix"])
    exporter = Path(config["exporter"])
    if not command:
        raise ValueError("missing command")
    if command[0] in {"lake", str(lean / "bin/lake")}:
        if config.get("verification_only"):
            raise ValueError("build forbidden during prebuilt verification")
        if command[1:] not in (["build", config.get("challenge_module", "LeanSphincs.Benchmark.Challenge")],
                              ["build", config.get("solution_module", "LeanSphincs.Submission.Solution")]):
            raise ValueError("unexpected Lake target")
        command[0] = str(lean / "bin/lake")
    elif command[0] not in {str(lean / "bin/leanchecker"), str(exporter)}:
        raise ValueError("unexpected comparator child")
    sandbox = landrun_args(Path(config["landrun"]), root, lean, exporter, command,
                           build=command[0] == str(lean / "bin/lake"),
                           submission_prefix=config.get("submission_prefix", "LeanSphincs.Submission"))
    os.execv(sandbox[0], sandbox)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, RuntimeError) as error:
        raise SystemExit(f"sandbox refused: {error}") from error
