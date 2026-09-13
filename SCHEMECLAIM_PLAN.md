# SchemeClaim: current plan and decision history

Status: draft v0.19 rules and implementation plan, 2026-09-13. The
[public rules](https://nconsigny.github.io/leansphincs/) and
[implementation contract](IMPLEMENTATION.md) describe the current target.
Historical notes below are snapshots, not competing current instructions.

## Latency-tail decision (2026-09-13, current)

The organizer accepts exceptionally slow operations with probability at most
2^-60. Normal latency targets remain 60 s keygen and 1.5 s signing; prove a
2^-60 overrun bound for each. Runs may take minutes within larger absolute
timeouts whose values remain to pin. This supersedes the earlier requirement
that the normal targets hold on every path. RAM remains a hard 64 KiB cap.

For signing, cover each request position under allowed adaptive message
selection. The planned probability space includes the ROM and keygen/signing/
adversary randomness. The exact performance game and adversarial query budgets
still need to be pinned. With a proved per-position bound, a union bound gives
at most N*2^-60 probability of any late signature in N requests, without
independence. This is not a lifetime 2^-60 promise.

Keep absolute runtime and raw-query caps on every path. Even a rare huge-query
branch can make the current pathwise security budget vacuous. The 2^-60
latency allowance does not relax signing failure (2^-128 in the R8 game) or
unforgeability; full proofs must include slow executions. Do not abort at the
normal latency target merely to satisfy the performance bound.

Before ranking/promotion: implement the resource/performance game and executable
binding; calibrate absolute and raw-query caps; prove latency, termination and
failure separately; test late valid outputs, excessive tail mass, absolute-cap
overruns and rare query-padding branches. `SchemeClaim` remains unchanged.

## Earlier bounded-honest-work decision (2026-09-13, superseded in part)

The following records the earlier strict-latency wording. The current decision
above replaces its per-path 60 s / 1.5 s requirement with latency-tail bounds.
Independent absolute limits and the query-padding exclusion remain required.

R9 now explicitly requires worst-case keygen <= 60 s, signing <= 1.5 s and
64 KiB working RAM. Charge every path, all required setup/precomputation and
all retries, including failure. A small probability of exceeding the cap is
not sufficient. Signing bounds cover every generated key and message and
successive requests. Ranked academic profiles must fix their own budgets.

The whole-experiment qH convention needs independent limits on honest work:
2^128 setup queries make a 128-bit work/probability slope trivial even for an
insecure scheme. Raw keygen/sign/verify caps must include empty and repeated
queries and keep honest overhead within the nontrivial security range.
`IMPLEMENTATION.md` records the corresponding profile-validation inequalities.

Priority before any ranking/promotion: implement the protected resource contract
and executable binding, calibrate caps, and add query-padding and runtime-overrun
rejection fixtures. The current mathematical claim remains unchanged and cannot
establish resource eligibility. The budget values were already decided; this
revision replaces the ambiguous “intended limits” wording with a mandatory rule.

## Current decisions: Benedikt review accepted, 2026-09-11

1. Both stages use `c * signatureBytes + verificationWork`, within separately
   pinned games and meters. c is an organizer-owned positive rational, pending
   calibration. No implicit price, no scalar ranking before calibration.
   The former product and four-factor objectives are superseded.
2. Complete-account normal latency targets are 1.5 s signing and 60 s keygen,
   now with 2^-60 overrun allowance per operation (September 13 decision above).
   Absolute runtime/raw-query caps and 64 KiB RAM still cover every path.
   Full-program bounds include retries and arithmetic.
   Hardware calibration, storage limits and component budgets remain open.
   Historical hash-throughput conversions are not resource certificates.
3. Pure-ROM, end-to-end Lean proofs only. No extra cryptographic assumptions,
   constants-dropping gate, named construction ban or separate proof-style rule.
   Internal modular reductions must discharge their own premises.
4. Security is SUF-CMA with total query work Q = qH + qS. qH counts the entire
   experiment including challenger hashes; qS counts failed/repeated requests.
   Bound length, coefficients and exponents are fixed independently of budgets.
5. One scheme, parameters and bound must satisfy 124 bits at 2^20 requests and
   100 bits at 2^32. The security theorem itself covers qS <= 2^32.
   The fixed-cap endpoint certificate is conservative even at Q < signingCap.
6. Public keys are at most 32 bytes. Successful signature size remains an
   equality. The single arbitrary-input/32-byte-output oracle and per-call
   `ceil(inputBytes / 64)` work remain unchanged.
7. Standard keygen/sign/verify structure; immutable preprocessing may live in sk.
   No mandatory separate cache/presign channel. Any public disclosure/replacement
   extension requires its own model; it is no longer on the core critical path.
8. Correctness on success and fixed-message fresh-key failure <= 2^-128 remain
   separate. Stronger 2^-256 certificates qualify. Adaptive lifetime availability
   is not inferred from this clause.
9. Academic Stage 1 is broader than OTS: few-time components, encodings,
   authentication, composition and complete constructions are also in scope.
   Standard hybrid multi-instance reductions may be used with their loss and
   actual shared-RO/domain-separation conditions accounted for.
10. Automatic numerical ranking and human-curated research/negative-result
    credit are separate. No QROM formalization promise or generic classical/2
    guarantee. Final award/adoption approval is still pending.
11. GitHub remains canonical under the existing organizer decision; agent
    publication instructions live in AGENTS.md, not the rules page.

## Implemented protected statement

```lean
structure SchemeClaim (S : SigScheme)
    (sigmaBytes hVerify : Nat) (coeffs : BoundCoeffs) : Prop where
  correct         : CorrectOnSuccess S
  signing_failure : HasSigningFailureBound S 128
  sigma_positive  : 0 < sigmaBytes
  sigma_size      : HasSignatureSize S sigmaBytes
  public_key_size : HasPublicKeySize S 32
  hverify_positive : 0 < hVerify
  verify_queries  : HasVerificationBound S hVerify
  security        : ∀ A qH qS, qS ≤ 2^32 →
    HasHashQueryBound S A qH → HasSigningQueryBound A qS →
    sufAdvantage S A ≤ boundProbability coeffs (qH + qS) qS
  floor           : MeetsFloor coeffs (2^20) 124
  decay_floor     : MeetsFloor coeffs (2^32) 100
```

Explanatory expansion of the constants; the normative file is
`LeanSphincs/Benchmark/Claim.lean`. The comparator leaves only S as a definition
hole and binds all three declarations. The claim identifier is
`suf-cma-total-work-pk32-decay-v1`; meter `rom256-input64-ceil-v1` is unchanged.
Old declarations/receipts need re-verification, not relabeling.

The exact evaluator and its convex endpoint proof remain independent of VCVio.
The new signing-budget monotonicity lemma and `SchemeClaim.security_le` /
`.decay_le` prove both advertised total-work inequalities. Regression fixtures
exercise the smaller key cap, separate decay certificate and constants ambiguity.

## Workstreams and next priorities

- **WS1: library coordination.** HashSig oracle-ization is independent of the
  statement. Coordinate with Quang/Alex and Emile's SPHINCS/OTS work; do not
  silently move the reproduced reference pin or duplicate his active work.
- **WS2: oracle, interface and game.** Implemented. No new cache/epoch interface
  is needed for the core syntax. Keep raw queries separate from weighted work.
- **WS3: fixed bounds.** Implemented with exact endpoint and monotonicity proofs.
  Keep all constants. Any future tighter feasible-budget gate requires a new
  theorem and explicit versioning, not a silent change to this certificate.
- **WS4: claim, comparator and pricing.** Revised claim and organizer-owned
  additive profile implemented. An unset c issues no scalar score; all local
  receipts stay unranked. Full execution and S/K budget binding remain to add.
- **WS5: production negative tests.** Existing real-comparator canaries and
  actual-claim rejection fixtures are diagnostic coverage. Complete the matrix
  by mutating a genuinely accepted baseline, including both lifetime fields.
- **WS6: baseline #0.** An eligible **SPHINCS⁻ variant**, not a weakened target.
  The pinned 126-bit theorem at 2^24 requests is promising, but still needs
  byte serialization, game/query transport, weighted verification, failure
  probability and a same-parameter security extension to 2^32 requests.
  Passing numerical floor examples does not finish that extension.
- **Academic targets.** With Emile, pin the first component game and per-track
  budgets without limiting Stage 1 to OTS or assuming a fully black-box use.
  Existing graph, counting and failure-envelope code is experimental.
- **Execution and launch.** Bind the executable to the Lean algorithms, account
  for full arithmetic/memory/retries and establish worst-case resource bounds.
  Calibrate c and the wallet profile, set storage/verifier caps, then finish
  baseline validation, governance, external audit, verifier registration and
  authenticated frontier promotion before opening submissions.

The 124-bit floor is unchanged; any future higher-floor proposal needs a separate
decision and baseline evidence. Repo governance, prizes and timeline remain open.
No lower-security launch workaround is authorized by this plan.

## Validation of the reviewed implementation (2026-09-11)

84 host tests pass, including pricing provenance, rejection of entrant-owned
pricing, the fixed 128-term limit and current website rules. The complete
`lake build LeanSphincs LeanSphincsTest` succeeds (3313 jobs); protected and
experimental OTS axiom audits admit only the three standard axioms.
The strict Linux profile passes all 11 boundary probes, all five metric
comparator canaries and all four actual-claim rejection cases (forged axiom,
sorry, weakened statement and oracle escape). Rejected receipts bind the new
claim identifier and null organizer price and contain no score. Desktop/mobile
page previews were checked. These are local diagnostics, not a cryptographic
baseline, external audit, remote-CI result or deployment certificate.

## Historical working notes (superseded where inconsistent above)

The following notes preserve prior decisions, estimates and validation dates.
References to older objectives, auxiliary channels, constants-dropping rules,
hash-to-time conversions or publication targets are historical only.

## Local implementation progress (2026-09-06)

2026-09-10, v0.15 meter decision: arbitrary byte-string input, fixed 32-byte output,
with `ceil(inputBytes / 64)` work per call, charging supplied domain-separation
bytes. The literal ceiling assigns zero weight to empty input; raw security
query counts and cycle accounting remain separate. This updates the protected
`hashWeight` and invalidates cross-meter score comparisons, not the SUF-CMA
game or proof assumptions. Receipts identify `rom256-input64-ceil-v1`;
experiments use `rom32-input64`, preserving `rom32` as a historical profile.
Boundary, repeat-charge and empty-query-budget regressions are included in Lean
and host tests. The source-level annex and PR #19 estimates become 810 keygen
units and 531 verification units respectively, not accepted cost certificates.
Under fixed size/signing constraints, verification-minimizing search must allow
Reed–Solomon-coded candidates, with no presumption that chains are optimal.

2026-09-10, v0.16 decision: the objective returns to `size * verification`.
Signing work and keygen work are fixed as hard budgets rather than scored: signing
stays at 1.5 s, keygen moves from 45 s to 1 minute at the 160 MHz anchor (hash-work
view: about 8.5 × 10^4 and 3.4 × 10^6 units). The oracle meter is unchanged
(`ceil(inputBytes / 64)`, 32-byte output). Stage 1 is framed as academic research
on pure hash work; Stage 2 is the Ethereum selection. The v0.14 four-factor
objective and beta = 1/4 are superseded; the OTS experiment CLI keeps its rank key
as a research view only. The Stage 1 board gets two tabs, Spacetime (ranking) and
Pareto (size/verification frontier at the fixed budgets). The legacy
`sigma * hverify` score now coincides with the objective; the S/K budget
certificates and their comparator binding remain to implement.

2026-09-10, v0.14 decisions and publication: apply the four-factor objective with
beta = 1/4 to both stages, retain hard usability gates and existing 45 s / 1.5 s
wallet budgets, and expose full instruction/memory work alongside the hash view.
Polynomial/Reed–Solomon coding is not excluded for being algebraic, but its
correlations and execution costs must be proved/metered. The final prize profile,
cycle weights/caps and signing-work quantifier remain open. Website v0.14 is
maintained on GitHub, now canonical by explicit organizer decision (2026-09-10).
The earlier Claude artifact is a legacy copy, no longer a synchronized target;
publication proceeds from this repo's `main` branch without waiting for it. The protected
legacy claim is unchanged and does not certify the new K/S factors.

Validation for v0.14: 62 Python tests passed (including website decision/link
checks and annex arithmetic), `lake build LeanSphincs LeanSphincsTest` succeeds,
and both protected/experimental axiom audits admit only standard axioms. Desktop
and 390-pixel mobile previews were checked locally. None of these checks is a
deployment, a complete cycle certificate or acceptance of a cryptographic entry.

Next execution-accounting work, coordinated with Emile rather than changing his
OTS construction interface prematurely:

1. Pin separately identified hash-work and execution profiles, including query
   byte layouts, instruction/memory accounting, signing-work quantifiers and
   setup/delegation treatment. No fixed conversion from abstract hash-work units to
   concrete compression blocks or cycles is assumed.
2. Build an encoding-kernel comparison on matched profiles: existing chain/
   codebook operations and the supplied polynomial shape when its full algorithm
   is available. Retain operation counts, measured timings and proved bounds as
   distinct evidence; no hash-only result establishes a latency improvement.
3. Bind the executable to the Lean oracle scheme, then prove complete K/S/V and
   memory bounds, including malformed inputs and bounded retry exhaustion.
   Connect the failure-envelope premise to the actual adaptive ROM/cache game.
4. Version the stage-specific claim and comparator to bind the two score factors and the signing/keygen budget certificates.
   Keep the current three-file MVP unranked until that transition and the
   baseline/launch gates are complete. See [annex review](POLYNOMIAL_CODING_REVIEW.md).

2026-09-09 OTS exploration: the organizer requests a four-factor objective
`size * signing * verification * keygen^beta`, with lower keygen weight. Beta = 1/4
is now approved; expected-versus-worst-case signing semantics remain pending. Experimental exact
ranking, Lean graph/cost foundations and a re-metered fixed-family counting engine
are implemented separately from the protected MVP. See [OTS_STAGE1.md](OTS_STAGE1.md)
for evidence, assumptions and the remaining security/composition proof milestones.
Neither the full-scheme score nor the published spec changes in this batch.
The next increment adds actual byte-level graph oracle evaluation, injective
address/value encoding and a worst-case weighted-query theorem, including
missing-input rejection and repeated gates. Graph correctness, codebook decoding,
availability and strong one-time security remain separate unfinished obligations.
The subsequent increment proves reconstruction under an oracle-consistent
reference and adaptive failure envelopes with explicit exception allowances.
The requested worst-case probability treatment is documented in OTS_STAGE1.md;
it is not a claim that the concrete signer satisfies the freshness premise or
that a single-request bound automatically extends to an entire key lifetime.

2026-09-09 shipping progress: receipt integrity and SIGTERM handling were committed
and pushed unsigned in `e639597` (no co-author trailer). The next harness batch
adds per-checkout admission locking and retryable `worker_busy` receipts before
candidate access, with 45 host tests. This advances worker admission, not the
remaining external scheduler, aggregate disk quota or cryptographic baseline.

2026-09-09 independent harness work: cooperative CLI SIGTERM cleanup now follows
the interruption path, with process-group and systemd-stop regression coverage
(37 host tests). The OTS target, composition contract and audited reference pin
remain untouched. Emile's branch advanced to
[`68a0bac`](https://github.com/leanEthereum/leanVM-b/commit/68a0bacd9fb8456a8a4c25717cbb83bf9ea6c5fc),
whose commit report leaves the public 126-bit statement unchanged and the final
127-bit theorem open. That revision has not been rebuilt locally here.

2026-09-08 independent harness work: receipts now recheck dependency pins and
tool hashes before scoring and publish complete JSON atomically; 33 host tests
cover integrity drift, orchestration failures and receipt publication. The core
and first sandbox hardening were committed in `31a5f92`; spec v0.13 followed in
`4ae1d37`. These receipt changes do not modify the protected Lean claim.

Coordination: leave the proposed OTS target and composition contract open while
Emile (GitHub `TomWambsgans`) completes his exploration. Monitor
[sphincs-fv](https://github.com/leanEthereum/leanVM-b/tree/sphincs-fv) before
integration; do not move the reproduced PR #19 pin automatically. The branch
snapshot `990b2ce5fa1ee99d8a0797da163db46bc498cf7f` reports reduction improvements
and explicitly leaves the final 127-bit inequality open. This is an upstream
commit report, not a local reproduction of that revision.

2026-09-07 harness advance: per-run source capture and isolated build outputs,
read-only protected/dependency caches, mandatory Linux sandbox probes and
content-bound receipts are implemented. All four real `SchemeClaim` rejection
cases and all five metric-only canaries pass in the strict Linux profile; 22
host tests pass. See [HARNESS_SECURITY.md](HARNESS_SECURITY.md).
This advances WS5 without claiming baseline #0, external audit, registration or
production freeze is complete.

WS2, WS3 and WS4 now have a staged implementation in this checkout, documented in [IMPLEMENTATION.md](IMPLEMENTATION.md). The protected Lean library builds on Lean 4.31.0 / VCVio `cbd4144b51d92da00dd50f05e068b2348fa6e529`; its axiom audit admits only the three standard axioms. The exact rational floor predicate has a proved two-endpoint characterization. The comparator has one scheme-definition hole and binds all three declared metric files. Organizer canaries exercise successful matching, rejection of each changed metric, and forbidden-axiom rejection; they are not baseline #0.

Verified again on 2026-09-07 after the previous session was cut off: the protected library builds, the axiom audit passes, the ten host-side contract tests pass, the signing-failure regression fixtures (always-failing signer rejected, invalid successful output rejected, failed requests charged to the signing budget, `none` never counts as replay) compile, the five comparator canary fixtures were recreated for the `Option Bytes` signing interface and all five real-comparator runs return the expected verdicts, and the PR #19 126-bit endpoint was reproduced locally with a standard-axiom footprint (see PR19_REVIEW.md). A `LeanSphincsTest.lean` root now lets `lake build LeanSphincsTest` succeed. This work was subsequently committed in `31a5f92`.

The WS2 block convention is now pinned to `ceil(inputBytes / 64)`, charging all supplied bytes, including domain separation, with zero weight for empty input. This supersedes the staged 32-byte input unit and one-unit minimum. The canonical GitHub spec source is v0.15 (2026-09-10), retaining the signing-failure decision introduced in v0.13. Repo home and merge rights remain deferred.

[leanVM-b PR #19](https://github.com/leanEthereum/leanVM-b/pull/19) supplies an additional, directly relevant stateless SUF-CMA proof route: a public 126-bit statement at 2²⁴ signing requests, with the same whole-experiment ROM accounting. See [PR19_REVIEW.md](PR19_REVIEW.md). It can shorten WS6 without waiting for WS1, but needs serialization, game/cap transport and block-weighted verification proofs. Its signer returns `Option Signature` after bounded grinding. Following discussion with Emile and organizer approval on 2026-09-06, the staged contract now admits explicit signing failure, with separate correctness-on-success and failure-probability ≤ 2⁻¹²⁸ obligations. This is a per-fixed-message, fresh-key/shared-ROM gate, not an adaptive lifetime guarantee. Baseline transport and production validation remain; the contract is not yet frozen for submissions.
