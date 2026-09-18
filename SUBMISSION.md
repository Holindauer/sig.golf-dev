# MVP submission contract

Status: implementer guide for draft v0.22, not an open competition.
The protected claim identifier remains `suf-cma-total-work-pk32-adaptive-availability-v2`.
The three-file format remains, but security semantics and lifetime coverage have
changed. The organizer-owned product score needs no price coefficient; receipts
remain diagnostic and unranked, with deployment eligibility false. Signing/keygen and
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
- Structural raw hash-query caps on every response path, including responses
  the random oracle never returns: key generation at most `rawKeygenCap = 2^28`
  calls, each signing request at most `rawSignCap = 2^20` for every secret-key
  value and message, verification at most `rawVerifyCap = 2^16` including empty
  calls. Two uniform-sampling caps bound the randomness draw: key generation at
  most `sampleKeygenCap = 2^28` and each signing request at most `sampleSignCap = 2^20`
  uniform queries (verification cannot sample). Straight-line algorithms discharge
  all of these with `isQueryBoundP_pure` and the bind lemmas; data-dependent loops
  need a fixed iteration cap.

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

R9 requires Pr[T_keygen > 60 s] <= 2^-40 and Pr[T_sign > 1.5 s] <= 2^-40,
with 64 KiB working RAM on every path. Signing must cover each request position
under permitted adaptive message selection in the bounded-query performance
game; an average over random messages does not suffice. The precise game and
adversarial budgets remain to pin. The allowance is per operation, not lifetime.

Runs may continue up to 120 s signing and 360 s keygen, absolute limits on every
path with no probabilistic exception. Keygen must return a usable key by its limit.
All setup and retries, including failures, count. A late signature must remain
valid; crossing the normal target does not trigger automatic failure. Any
failure at the absolute timeout must fit the separate R8 failure bound of 2^-128.
Every execution path must meet the absolute runtime and raw-query caps, including
repeated and empty-input calls. Slow branches remain inside the security proof.

Whole-experiment qH includes honest work: if keygen always makes 2^128 queries,
Adv <= Q/2^128 is trivial for every admissible budget, even for an always-accepting
verifier. A positive signature-size requirement does not cure that problem.
Resource bounds must therefore be checked independently of the security slope.
A rare huge-query branch can also inflate the pathwise qH bound; the 2^-40
latency envelope alone cannot exclude that loophole.

The three-file mathematical contract now enforces the structural raw-query caps
but still lacks the runtime, storage and executable certificates. Its local
accepted receipt is insufficient for ranking or promotion. The next
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
reduced; exponents are bounded by work `a ≤ 32`, sign `b ≤ 64` and `k ≤ 1024`;
terms are unique and sorted by `(a,b,k)`. In Lean, the example is `[⟨4, 0, 1, 0, 128⟩]` because the denominator
uses predecessor encoding. It represents a 126-bit total-work slope, but
declaring it is not a proof that your scheme satisfies it at either lifetime.
The list length, coefficients and exponents must be fixed independently of Q/qS.

The fixed-cap certificate checks the whole interval starting at Q = 1, including
infeasible Q < signingCap points. It is conservative, and evaluation is monotone
in qS. The security theorem must cover the extended request range itself.

The objective is the exact integer `sigma * hverify`, minimized, with
signature size as the tie-break. Its units are bytes × verification-work units.
The rule comes only from `benchmark/scoring.json`; no bandwidth coefficient or
entrant price file is admitted. Scores are diagnostic and do not establish
deployment eligibility. Keep both coordinates for Pareto comparisons. No
additional scored file is needed for signing availability.

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

## Current contract: hardening retained in v0.22

`Availability.lean` reuses the signing oracle in a shared-ROM interaction with
adaptive messages and an ordered response log. `SchemeClaim` now requires
`adaptive_failure` and `adaptive_decay_failure` as well as the fresh-key,
fixed-message certificate. Failure at zero-based position i means that request i
occurs and returns `none`; absent positions are not failures. Its unconditional
probability includes keygen, ROM and participant randomness, and is at most
2^-128 for every permitted position: up to 2^20 requests / Q <= 2^124, and up to
2^32 requests / Q <= 2^100. Q counts all interaction raw hashes (including keygen
and honest signing) plus requests; it excludes final forgery verification.
Structural query bounds quantify over every response path. Stronger thresholds
transport, and the union bound gives at most 2^-96 over 2^32 positions, not 2^-128.
The SUF-CMA experiment and its final-verification accounting are unchanged.

Protected claim ID: `suf-cma-total-work-pk32-adaptive-availability-v2`. Historical
receipts must be rerun, never relabeled as certificates for this claim.

The runner compiles in a separate constrained systemd service, confirms the
whole service has stopped, then captures declared regular Lean artifacts into
`verification/`. Kernel checking, export, comparison and axiom auditing use
`--verify-prebuilt`, which invokes no build. The verification child has no
candidate write grants. Artifact filenames, sizes and hashes are recorded and
rechecked before receipt publication. Source scanning rejects `eval%` and unsafe
helpers as defense in depth; compilation can execute code even if scanning passes.
Source pins do not authenticate precompiled dependency caches.

`benchmark/resources.json` is organizer-owned. Reference execution calibration,
verification limits, raw keygen/sign/verify caps, persistent secret and
precomputation storage, executable size and evidence validators remain unset.
Missing values fail closed. Execution evidence must bind algorithms, executable
and profile, including malformed-input rejection, parsing, arithmetic, randomness,
retries and setup. Structural raw-query certificates must include impossible-ROM
response branches; ROM-consistent measurements alone cannot certify them.
Storage evidence counts serialized secret/precomputation bytes and documents key
restoration. RAM is no substitute. Independent side-channel implementation review
must state a timing/memory-access leakage model and bind executable and profile;
this is not a formal noninterference theorem.

Executable resource validation is unimplemented: deployment eligibility remains
false even with supplied evidence. Receipts separate mathematical verification,
resource certification, side-channel review and deployment eligibility and keep
`ranked: false`. Any diagnostic score is explicitly non-eligible.
The organizer product profile is the only competition scoring authority. Successful
verification issues an exact diagnostic size × verification-work score without
a bandwidth coefficient; deployment remains blocked. Existing latency targets,
2^-40 overrun allowances, absolute deadlines and 64 KiB RAM cap are unchanged.
Positive metric/availability fixtures are not cryptographic baselines. Emile's
upstream pin, OTS construction work and baseline parameters are unchanged.

## Submitting through the site

Once admission is `open` in `challenges.json`, the way in is a pull request against the contract
repository that changes only `submissions/full/`. The hosted verifier runs `scripts/verify_pr.py`
on the head commit and answers as a commit status and a comment; a verified head becomes a record
only when that exact head is merged. Check locally first: `python3 scripts/verify_pr.py full --source . --json`.
