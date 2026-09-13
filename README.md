# leanSPHINCS

The [competition rules](https://nconsigny.github.io/leansphincs/) are draft
**v0.18**, with mandatory keygen/signing resource limits. Stage 1 covers academic research
beyond OTS: primitives, encodings, authentication, composition and complete
constructions. Stage 2 evaluates complete stateless Ethereum account signatures,
complementing the leanSig consensus track.

Both use **`c * signatureBytes + verificationWork`**, within separately pinned
games and cost profiles. The positive rational bandwidth price `c` is not yet
calibrated: no default price or scalar ranking is issued. The mandatory account
limits remain **1.5 s signing, 60 s keygen and 64 KiB working RAM**. Complete-program
certificates and hardware/storage calibration remain unfinished; hash throughput
does not certify seconds.

R9 requires these worst-case limits on every execution path, including failed
retries and all required setup. Missing resource certificates exclude ranking
and promotion. Raw-query caps must also prevent honest algorithms from consuming
the security budget through query padding, including zero-weight empty queries.
These caps and their protected executable binding still need implementation.

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
  probability at most 2^-128. This is not adaptive lifetime availability.
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
