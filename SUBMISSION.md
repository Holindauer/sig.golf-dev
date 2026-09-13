# MVP submission contract

Status: implementer guide for draft v0.18, not an open competition.
The revised claim identifier is `suf-cma-total-work-pk32-decay-v1`.
The three-file format remains, but security semantics and lifetime coverage have
changed. The additive price is organizer-owned and not yet calibrated; receipts
remain unranked and have no scalar score while it is unset. Signing/keygen and
full-program certificates remain launch work.

## Package

Provide a flat folder containing:

```text
Scheme.lean      algorithms against the protected oracle interface
Solution.lean    the exported SchemeClaim proof
sigma.txt       exact successful-signature byte length
hverify.txt     worst-case block-weighted verification bound
bound.txt       canonical security-bound coefficients
Helper.lean     optional; additional flat Lean helper modules are allowed
```

Use UTF-8 source, with filenames matching `[A-Za-z_][A-Za-z0-9_]*.lean`.
No build files, compiled artifacts, symlinks, subdirectories or executable tools
are admitted. The limits are 1,000 files, 4 MiB per file and 10 MiB total.

`Scheme.lean` imports `LeanSphincs.Benchmark.Target` and defines
`LeanSphincs.Submission.scheme : LeanSphincs.Benchmark.SigScheme`.
Local helpers are imported as `LeanSphincs.Submission.Helper`.
`Solution.lean` exports exactly `LeanSphincs.Benchmark.candidate` with type:

```lean
LeanSphincs.Benchmark.SchemeClaim LeanSphincs.Submission.scheme
  sigmaBytes hVerify coeffs
```

Only the scheme definition is a comparator hole. The oracle, game, claim fields,
budgets, metric arguments and bound semantics must match the protected statement.
Permitted imports are the protected `Target`, pinned Mathlib/VCVio/HashSig, and
flat local helpers. Use one import per line in the initial import block. Custom
elaborators/macros, native_decide, build-time execution and kernel-bypass features
are rejected. All theorem/algorithm axiom closures must stay within `propext`,
`Classical.choice` and `Quot.sound`; `sorry` is not admitted.

## Proof obligations

- Correctness on success and, separately, signing failure probability ≤ 2⁻¹²⁸
  for every fixed 32-byte message under fresh key generation and a shared ROM.
  Signing returns `Option Bytes`; a stronger 2⁻²⁵⁶ certificate also qualifies.
- Exact positive signature size for every successful output, public-key size
  ≤ 32 bytes, and a positive verification bound covering malformed inputs too.
- A pure-ROM SUF-CMA bound `Adv <= B(qH + qS, qS)` for every admissible
  adversary at up to 2^32 signing requests.
- Both endpoint predicates on the same scheme and bound: 124 bits at 2^20
  requests and 100 bits at 2^32. No reparameterization or constants dropping.

Failed signing responses are visible and count against the signing-query budget.
Only an exact successful message/signature pair is a replay. qH counts raw
hash queries across the whole experiment, including keygen, honest signing,
adversarial hashing and final verification. The polynomial uses total work
Q = qH + qS, where qS counts all signing requests; verification scoring instead charges
`ceil(inputBytes / 64)` per call, including domain-separation bytes. The output
remains 32 bytes; empty input costs 0 hash-work units but still consumes one raw
security query. This convention is pinned. Receipts identify it as
`rom256-input64-ceil-v1`; historical 32-byte-unit receipts are not comparable.
Rebuild cost certificates and regenerate receipts against the current statement.

## Mandatory resource certificates before eligibility

R9 requires worst-case keygen <= 60 s and signing <= 1.5 s, with 64 KiB working
RAM. Keygen covers all setup needed for a usable key; signing covers every
generated secret key, every message and every invocation path. All retries,
including failures, count. Expected runtime and rare overruns do not meet a
worst-case limit. Each profile must also fix raw-query caps for keygen, signing
and verification, counting repeated and empty-input queries.

Whole-experiment qH includes honest work: if keygen always makes 2^128 queries,
Adv <= Q/2^128 is trivial for every admissible budget, even for an always-accepting
verifier. A positive signature-size requirement does not cure that problem.
Resource bounds must therefore be checked independently of the security slope.

The current three-file mathematical contract lacks these resource certificates.
Its local accepted receipt is insufficient for ranking or promotion. The next
protected resource contract must bind the actual algorithms/executable and
organizer caps before ranked submissions open; do not invent extra entrant files
for this still-unimplemented interface.

## Declared metrics

`sigma.txt` and `hverify.txt` each contain one positive ASCII decimal integer
(≤ 2⁶³−1), without leading zeros or whitespace other than an optional final LF.
`bound.txt` is a JSON array of 1–128 terms:

```json
[[4,1,1,0,128]]
```

Each term `[numerator, denominator, a, b, k]` denotes
`(numerator / denominator) * Q^a * qS^b / 2^k`. Fractions must be positive and
reduced; exponents are natural numbers ≤ 1024; terms are unique and sorted by
`(a,b,k)`. In Lean, the example is `[⟨4, 0, 1, 0, 128⟩]` because the denominator
uses predecessor encoding. It represents a 126-bit total-work slope, but
declaring it is not a proof that your scheme satisfies it at either lifetime.
The list length, coefficients and exponents must be fixed independently of Q/qS.

The fixed-cap certificate checks the whole interval starting at Q = 1, including
infeasible Q < signingCap points. It is conservative, and evaluation is monotone
in qS. The security theorem must cover the extended request range itself.

The objective is the exact rational `c * sigma + hverify`, minimized, with
signature size as the tie-break. c comes only from the protected organizer profile
`benchmark/scoring.json`. It is currently null; no scalar score is emitted.
Do not submit a price file or claim a calibrated ranking. No additional scored
file is needed for signing availability.

## Local verification

```sh
bash setup.sh
bash benchmark.sh /absolute/path/to/submission
```

The final line points to a retained `result.json`, captured inputs and logs.
Editing the original folder after capture does not change what was verified.
Each run has fresh candidate build outputs. An `accepted` local result is still
unranked: no remote verifier has registered, audited or promoted it.

Only one verification is admitted per checkout. A `worker_busy` result is
retryable, exits nonzero and does not read or reject your candidate; retry after
the current run finishes. Do not delete `.worker.lock` to bypass admission.

If sandbox setup fails, fix the host using [HARNESS_SECURITY.md](HARNESS_SECURITY.md).
Do not treat the explicit `--insecure-local` option as a substitute for the
competition verifier; it is for organizer-owned diagnostics only.

No complete accepted example is provided yet. The metric canaries are deliberately
not security proofs. Baseline #0 is the next end-to-end cryptographic deliverable.
