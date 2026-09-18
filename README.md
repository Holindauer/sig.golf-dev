# leanSPHINCS

The [competition rules](https://leanethereum.github.io/leanSphincs/) are draft
**v0.22**, with latency guarantees and absolute resource limits. Stage 1 covers academic research
beyond OTS: primitives, encodings, authentication, composition and complete
constructions. Stage 2 evaluates complete stateless Ethereum account signatures,
complementing the leanSig consensus track.

Both use **`signatureBytes * verificationWork`**, within separately pinned
games and cost profiles. The product has byte × verification-work units, needs
no bandwidth coefficient, and accompanies the full size/verification Pareto frontier.
Local scores remain diagnostic and unranked; deployment gates still apply. Normal account latency
targets are **1.5 s signing and 60 s keygen**, each with overrun probability
at most **2^-40 per operation**. Working RAM is bounded by **64 KiB** on every path. Complete-program
certificates and hardware/storage calibration remain unfinished; hash throughput
does not certify seconds.

R9 permits exceptionally slow runs up to absolute limits of **2 minutes signing
and 6 minutes keygen**, with no overrun allowance at those limits.
Absolute runtime/raw-query caps apply on every path,
including all setup and failed retries; even rare query padding must not make
the security bound vacuous. Lateness is separate from signing failure, whose
existing bound remains 2^-128. A union bound over 2^32 requests permits at most
1/256 probability of any late signature, not a lifetime 2^-40 guarantee.
Structural raw hash-query caps on keygen, signing and verification are fields
of the claim with uncalibrated placeholder values. The performance game, cap
calibration and protected executable binding remain to implement before ranking
or promotion.

## What is implemented

- A scheme-parametric, classical **pure-ROM SUF-CMA** claim with no additional
  cryptographic assumptions.
- Byte-level algorithms: keygen returns `(pk, sk)`, signing returns `Option Bytes`,
  verification consumes bytes. Immutable precomputation may live in `sk`; there
  is no mandatory auxiliary cache/presign interface.
- **32-byte public keys**, exact successful signature size, and a worst-case
  weighted verification bound including malformed inputs.
- **Total query work `Q = qH + qS`**. Raw `qH` includes challenger keygen,
  signing and final verification as well as adversarial hashes; `qS` includes
  failed and repeated signing requests.
- A fixed explicit exact-rational bound with proved endpoint certificates:
  **124 bits at up to 2^20 requests and 100 bits at up to 2^32**, for the same
  scheme, parameters and bound. No constants-dropping eligibility gate.
- Separate correctness-on-success and fresh-key, fixed-message signing failure
  probability at most 2^-128, plus adaptive per-position availability in both
  budget regimes. The 2^32-request lifetime union bound is 2^-96.
- A private-snapshot verifier, protected comparator, axiom checks and content-bound,
  explicitly unranked receipts. The organizer-owned
  [scoring profile](benchmark/scoring.json) is included in receipt provenance.

The oracle accepts arbitrary bytes and returns 32 bytes. Meter
`rom256-input64-ceil-v1` charges `ceil(inputBytes / 64)` **per call**, including
supplied domain tags. Empty input costs zero weighted work but one raw security
query. Full-program arithmetic and memory costs are separate.

## Development and remaining gates

```sh
python3 -m unittest discover -s tests
lake build LeanSphincs LeanSphincsTest
lake env lean scripts/check-axioms.lean
lake env lean scripts/check-ots-axioms.lean
python3 scripts/test-comparator.py
```

For the strict Linux submission path, run `bash setup.sh`, then
`python3 scripts/test-verifier.py` and
`bash benchmark.sh /absolute/path/to/candidate`.
Landlock ABI >= 8, a user systemd manager and passing active boundary probes are
required. `BENCHMARK_INSECURE_LOCAL=1` is an explicit organizer-only diagnostic,
never an automatic fallback.

**Submissions are not open. No cryptographic baseline is accepted yet.**
Positive comparator fixtures prove metric matching only. Baseline #0 is intended
to be an eligible SPHINCS⁻ variant; the pinned 126-bit proof at 2^24 requests still
needs an extended-lifetime argument for the same scheme at 2^32, in addition to
serialization, game/cost transport and signing-failure proofs.

See [submission format](SUBMISSION.md), [implementation contract](IMPLEMENTATION.md),
[workstream plan and decision history](SCHEMECLAIM_PLAN.md),
[PR #19 review](PR19_REVIEW.md), [experimental OTS foundations](OTS_STAGE1.md),
[polynomial-coding review](POLYNOMIAL_CODING_REVIEW.md) and
[harness trust boundary and launch gates](HARNESS_SECURITY.md).
Publication mechanics and agent conventions live in [AGENTS.md](AGENTS.md).

## Website and pull-request intake

The competition site (`service/`) shows the Spacetime ranking and the Pareto frontier, serves
`index.html` as the rules, and verifies pull requests that change only `submissions/full/` with
`scripts/verify_pr.py`. Admission is controlled by `challenges.json` and is closed until launch.
See [service/README.md](service/README.md) and [llms.txt](llms.txt).
