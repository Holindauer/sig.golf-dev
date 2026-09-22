#!/usr/bin/env python3
"""Exercise the real comparator with a non-security canary and negative cases.

Only organizer-owned fixtures are run here, with an explicitly fake sandbox.
This cannot validate a SchemeClaim or establish a ranked result.
"""

import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / ".benchmark-tools/comparator"
env = os.environ | {
    "COMPARATOR_LEAN4EXPORT": str(TOOLS / ".lake/packages/lean4export/.lake/build/bin/lean4export"),
    "COMPARATOR_LANDRUN": str(TOOLS / "scripts/fake-landrun.sh"),
}
config = json.loads((ROOT / "benchmark/comparator.json").read_text())
config.update(challenge_module="LeanSphincsTest.Challenge",
              theorem_names=["LeanSphincsTest.candidate"],
              definition_names=["LeanSphincsTest.Submission.scheme"])
output = ROOT / "benchmark-results/canary"
output.mkdir(parents=True, exist_ok=True)

for case, expected in [
    ("Good", "Your solution is okay!"),
    ("WrongSigma", "theorem statement do not match"),
    ("WrongMetrics", "theorem statement do not match"),
    ("WrongBound", "theorem statement do not match"),
    ("SmuggledAxiom", "Illegal axiom detected"),
]:
    config["solution_module"] = f"LeanSphincsTest.Submission.{case}"
    config_path = output / f"{case}.json"
    config_path.write_text(json.dumps(config))
    result = subprocess.run(["lake", "env", str(TOOLS / ".lake/build/bin/comparator"),
                             str(config_path)], cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    (output / f"{case}.log").write_text(result.stdout)
    if (result.returncode == 0) != (case == "Good") or expected not in result.stdout:
        raise SystemExit(f"{case}: unexpected result; see {output / (case + '.log')}\n{result.stdout}")
    print(f"{case}: expected {'acceptance' if case == 'Good' else 'rejection'}", flush=True)
