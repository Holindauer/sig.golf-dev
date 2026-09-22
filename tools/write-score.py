#!/usr/bin/env python3
"""Legacy declared-metrics calculator, NOT verification evidence or promotion.

The production runner binds proofs and scores in its own result.json. This
standalone helper can check metric consistency only, not comparator success.
"""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verifier"))
from benchmark_contract import metrics
from oracle_meter import meter_metadata
from scoring_policy import CLAIM_ID, load_scoring_profile, score_entry

if len(sys.argv) != 3:
    raise SystemExit("usage: write-score.py SUBMISSION_DIR RENDERED_SNAPSHOT")
snapshot = json.loads(Path(sys.argv[2]).read_text())
sigma, hverify, bound = metrics(Path(sys.argv[1]))
if snapshot != {"sigma": sigma, "hverify": hverify, "bound": bound}:
    raise SystemExit("declared metrics changed after rendering; no score issued")
profile = load_scoring_profile(Path(__file__).resolve().parents[1] / "verifier/scoring.json")
report = {
    "profile": "declared-metrics-only", "ranked": False, "verified": False,
    "claim_version": CLAIM_ID, "scoring_profile": profile,
    "hash_meter": meter_metadata(),
    "sigma": sigma, "hverify": hverify, "bound": bound,
}
report["score"] = score_entry(profile, sigma, hverify)
print(json.dumps(report))
