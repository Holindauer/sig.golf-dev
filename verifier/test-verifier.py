#!/usr/bin/env python3
"""Production-path rejection tests. These are NOT accepted cryptographic baselines."""

import argparse
import json
from pathlib import Path
import tempfile

from source_bundle import materialize
from verify_submission import verify

SCHEME = """import LeanSphincs.Benchmark.Target
noncomputable def LeanSphincs.Submission.scheme : LeanSphincs.Benchmark.SigScheme :=
  { SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some [0]), verify := fun _ _ _ => pure false }
"""
CLAIM = "LeanSphincs.Benchmark.SchemeClaim LeanSphincs.Submission.scheme 1 1 [⟨4, 0, 1, 0, 128⟩]"
PREFIX = "import LeanSphincs.Submission.Scheme\n"
CASES = {
    "smuggled_axiom": (PREFIX + f"axiom fake : {CLAIM}\n"
        f"theorem LeanSphincs.Benchmark.candidate : {CLAIM} := fake\n", "Illegal axiom detected"),
    "sorry": (PREFIX + f"theorem LeanSphincs.Benchmark.candidate : {CLAIM} := by sorry\n",
              "Illegal axiom detected"),
    "weakened_statement": (PREFIX + "theorem LeanSphincs.Benchmark.candidate : True := by trivial\n",
                           "theorem statement do not match"),
    "oracle_escape": (PREFIX + "def escape : OracleComp LeanSphincs.Benchmark.OracleWorld Unit :=\n"
                      "  IO.println \"outside oracle\"\n", "type mismatch"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--insecure-local", action="store_true")
    parser.add_argument("--case", choices=CASES)
    args = parser.parse_args()
    selected = {args.case: CASES[args.case]} if args.case else CASES
    for name, (solution, expected) in selected.items():
        with tempfile.TemporaryDirectory(prefix="leansphincs-negative-") as directory:
            source = Path(directory) / "source"
            materialize({"Scheme.lean": SCHEME.encode(), "Solution.lean": solution.encode(),
                "sigma.txt": b"1\n", "hverify.txt": b"1\n", "bound.txt": b"[[4,1,1,0,128]]\n"}, source)
            result, output = verify(source, args.insecure_local)
            log = output / ("compile.log" if name == "oracle_escape" else "comparator.log")
            if (result["status"] != "verification_failed" or "score" in result or
                    not log.exists() or expected.casefold() not in log.read_text().casefold()):
                raise SystemExit(f"{name}: unexpected {result['status']}: {result.get('error', '')}; logs: {output}")
            print(f"{name}: expected rejection, no score ({output})", flush=True)


if __name__ == "__main__":
    main()
