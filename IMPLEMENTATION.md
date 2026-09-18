# Statement and harness implementation contract

Status: implementation contract accompanying draft v0.22, 2026-09-15.
This is not a frozen competition, an accepted cryptographic baseline or a
deployment certificate. Historical decisions and validation snapshots are retained
in [SCHEMECLAIM_PLAN.md](SCHEMECLAIM_PLAN.md).

## Oracle and interface

`Oracle.lean` supplies arbitrary byte-list inputs and 256-bit outputs, with one
lazy ROM shared by key generation, adversarial hashing, signing and final
verification. Uniform sampling is separate. Verification work is the sum of
`(input.length + 63) / 64` over every call, including repeated and empty calls:
empty costs zero weighted units but still one raw security query. All supplied
domain tags count. Meter identifier: `rom256-input64-ceil-v1`.

`SchemeInterface.lean` fixes messages to 32-byte digests. A submission selects its
secret-key type and algorithms:
`keygen -> (pk, sk)`, `sign(sk, message) -> Option Bytes`,
`verify(pk, message, signature) -> Bool`.
Signing has no mutable state or epoch argument/output. Verification may hash but
does not sample random coins. Public keys and signatures are actual wire bytes.

Immutable precomputation may be included in the secret-key value. There is no
required auxiliary cache/presign interface or free 4 KiB cache allowance.
Disclosure/replacement/delegation needs a separately reviewed game extension;
secret/precomputation storage and complete-program resource bounds remain to bind.

`CorrectOnSuccess` requires probability one of either explicit failure or a
verifying output in the fresh-key experiment. Independently,
`HasSigningFailureBound S 128` bounds failure for every fixed message, averaged
over key generation, signing randomness and their shared ROM. The proved
`.mono` lemma transports a 256-bit certificate to the 128-bit gate.
This fixed-message certificate is additional to the adaptive predicate below; neither conditions on a key or transcript.

Exact signature size covers every successful output on every path from a
generated key; public keys are bounded by **32 bytes** on every keygen path.
The verification bound includes malformed inputs.

## Pure-ROM game and total work

`Game.lean` logs all signing requests and optional responses. Only an exact
successful message/signature replay is excluded; a different valid signature
on an already-signed message wins. Repeated and failed signing requests are
charged equally and are visible to the adversary.

`HasHashQueryBound` bounds raw calls across the **whole experiment**, including
challenger keygen, honest signing, final verification and adversarial hashing;
uniform sampling is excluded. `HasSigningQueryBound` bounds requests on every
adversarial path for every public key. These are not expected work bounds.

The security bound's first argument is **Q = qH + qS**, not just adversarial
hashing or weighted verification work. The actual game is unchanged; the claim's
accounting and theorem coverage are revised. Bounds are conservative when the
chosen budgets exceed actual query use.

Arbitrary pure computations are expressible. Eligibility requires an
unconditional, end-to-end ROM theorem with all internal reduction premises
discharged. There is no conjectural assumption registry, separate proof-style
exception or construction classifier by family name. Allowed axioms are exactly
`propext`, `Classical.choice` and `Quot.sound`.

## Resource bounds and nontrivial security budgets

R9 requires Pr[T_keygen > 60 s] <= 2^-40 and Pr[T_sign > 1.5 s] <= 2^-40.
Longer runs may complete within absolute limits of T_sign <= 120 s (2 minutes)
and T_keygen <= 360 s (6 minutes). These limits apply on every path with no
probabilistic exception. Keygen must return a usable key, not a timeout failure.
RAM stays bounded by 64 KiB on every path.
Charge setup/precomputation, arithmetic, randomness and all successful/failed
retries. Crossing the normal latency threshold does not automatically abort.

The planned performance game must quantify over allowed adaptive adversaries
and each signing-request position i. Its event is: request i occurs and its
runtime exceeds 1.5 s. Probability is over the shared ROM, keygen randomness
and execution randomness, including the adversary's random choices. This is
an unconditional bound for each position in that game, not a claim conditional
on every possible key or prior transcript. Averages over random messages are
insufficient. The precise game, adversarial raw-query budgets and program-cost
semantics remain to pin and implement before ranking.

Given that per-position bound, the probability of at least one late signature
in N requests is at most min(1, N*2^-40), without independence: at N=2^20 this is
2^-20, and at N=2^32 it is 2^-8 (1/256). Keygen has its own one-operation tail bound.
The allowance is not a 2^-40 guarantee over an entire key lifetime.

Late completion is separate from failure. Any signing timeout at the absolute
limit returns explicit failure and must be covered by R8's existing 2^-128
fresh-key/fixed-message bound. The full security proof must cover slow paths;
the 2^-40 latency allowance is not an extra permitted forgery probability.
`SchemeClaim` now carries three structural raw hash-query fields:
`keygen_queries` (`HasKeygenQueryBound S rawKeygenCap`), `sign_queries`
(`HasSignQueryBound S rawSignCap`, for every secret-key value and message) and
`verify_raw_queries` (`HasVerifyQueryBound S rawVerifyCap`, malformed inputs and
zero-weight empty calls included). They are conclusions the scheme proves, not
hypotheses of the security clause, and they bound every structural response
path, including answers the lazy random oracle can never return. Runtime and
executable binding remain unimplemented.

The whole-experiment accounting permits a vacuous security slope if honest work
already consumes the entire security range. With keygen fixed at 2^128 raw calls,
every admissible Q is at least 2^128, so Adv <= 1 <= Q/2^128 holds independently
of forgery resistance. Even a rare 2^128-query branch can force the pathwise
`HasHashQueryBound` budget that high. A high-probability runtime guarantee alone
does not close this loophole. The `sigma_positive` field rejects zero bytes,
but a padded trivial signature demonstrates the same accounting problem.

The resource profile must independently cap raw keygen, per-request signing and
verification calls (K, S, V), including repeated and empty queries. Its honest
work plus signing-request charges is bounded by K + qS*(S+1) + V. Profile
validation must keep that overhead within the nontrivial security ranges,
in addition to latency-tail and absolute runtime/memory checks. These raw caps
bound every path, including late executions. For the complete-scheme target, check
K + 2^20*(S+1) + V < 2^124 and K + 2^32*(S+1) + V < 2^100.
The pinned placeholders are `rawKeygenCap = 2^28`, `rawSignCap = 2^20` and
`rawVerifyCap = 2^16`, chosen with generous headroom over a SPHINCS-scale
construction; `honestWork_lt_floor` and `honestWork_lt_decay_floor` check both
inequalities in Lean. Two structural uniform-sampling caps, `sampleKeygenCap = 2^28`
and `sampleSignCap = 2^20`, bound the randomness draw of key generation and signing;
uniform queries are the `.inl` side of the oracle, outside qH, so the hash caps do
not see them, and a probability-zero path could otherwise draw unbounded randomness.
Verification is `HashSpec`-only and cannot sample. Calibration against the reference
execution profile remains open; no arbitrary raw-call-to-seconds conversion certifies
the fixed runtime limits. These five statement constants are mirrored by
`eligibility.STATEMENT_RAW_CAPS`, and `load_resource_profile` rejects any calibrated
`benchmark/resources.json` cap that disagrees with them, so the profile can never
drift from the proved caps. The same requirement applies to ranked academic profiles
under their own pinned games.

The tightened caps close vacuity and shrink the slack. Because Q counts honest work,
the certified bound for a low-effort adversary is B(K + qS*(S+1) + V): honest work is
about 2^40 at 2^20 requests and about 2^52 at 2^32 requests, giving certified floors
near 2^-84 and 2^-48 rather than the vacuous slope a 2^128 pad would force. A residual
slack remains inherent to counting honest work in Q; tighter calibrated caps, or a
bound stated over adversarial queries, would reduce it further, an organizer decision.

`LeanSphincsTest/DeadBranch.lean` is the regression: a scheme accepting every
signature whose keygen hashes the empty input twice and pads with 2^128 queries
only when the answers differ. `keygen_runtime` proves the padding is absent from
the random-oracle semantics, `almost_claim` proves every other clause, including
both adaptive availability clauses vacuously, and `no_claim` proves the keygen cap
rejects it. Before this field existed the local verifier issued an `accepted`
receipt for that scheme in both profiles.

Before opening ranking/promotion, bind these limits to the actual implementation
and add regressions for huge setup, signing and verification, including padding
with zero-weight empty queries, rare huge-work branches, violations of the
2^-40 latency envelope and overruns of the 120 s signing / 360 s keygen absolute
limits, including failed retries. Current local
mathematical acceptance remains unranked and cannot establish full eligibility.

## Fixed exact bound and lifetime certificates

A `BoundTerm` represents
`(numerator / (denominatorPred + 1)) * Q^a * qS^b / 2^k`.
The declared coefficient list is fixed independently of either query budget.
The host format enforces 1–128 positive reduced terms with bounded exponents;
the underlying mathematical evaluator also supports zero coefficients/empty
lists for general lemmas and tests.

For a fixed signing cap S and bit level b, `MeetsFloor` checks
`B(1,S) <= 2^-b` and `B(2^b,S) <= 1`.
Convexity of `B(Q,S) - Q/2^b` gives the full interval inequality.
`meetsFloor_iff` characterizes this **fixed-cap** interval exactly;
`evalBound_mono_signing` transports it to any smaller signing budget.

This includes numerical points Q < S. It is therefore a conservative sufficient
certificate for the feasible two-budget security region, not the tightest
possible test restricted to Q >= qS. No enumeration of 2^124 values is needed.
`bitSecurity` is reporting only; acceptance uses `MeetsFloor`.
`idealize` remains a historical arithmetic helper and is never an eligibility
predicate. Equivalent bounds must not acquire different eligibility by moving
powers of two between coefficients and denominators.

`SchemeClaim` requires one security theorem for all qS <= 2^32:
`Adv <= B(qH + qS, qS)`. It then checks both:

- `MeetsFloor coeffs (2^20) 124`;
- `MeetsFloor coeffs (2^32) 100`.

`SchemeClaim.security_le` and `.decay_le` derive the respective total-work
probability inequalities. Both refer to the **same S, parameters and coefficients**.
A theorem limited to 2^24 requests cannot supply the latter obligation just
because its polynomial numerically passes. `LeanSphincsTest/ReviewRules.lean`
checks the 32-byte boundary, separate decay gate and constants-dropping ambiguity.

There is no QROM gate, generic classical/2 guarantee or organizer commitment to
later formalize one.

## Comparator, declarations and pricing

The comparator's sole definition hole is the submitted `SigScheme`.
All other reachable statement definitions, including both floors, must match.
Algorithm and theorem axiom closures are audited.

The three declarations remain `sigma.txt`, `hverify.txt` and `bound.txt`.
The first two contain canonical positive integers <= 2^63-1.
Each bound row is `[numerator, denominator, a, b, k]`, with positive reduced
fraction, distinct monomials sorted by `(a,b,k)`, and exponents bounded by
work `a <= 32`, sign `b <= 64` and `k <= 1024`. Usable exponents are far smaller
(the floor forces `a <= 8`, `b <= 32`), so these caps reject no feasible bound while
bounding the kernel arithmetic the floor certificate reduces during rechecking; a
general expensive proof is bounded instead by the sandbox memory and runtime caps.
The first exponent now applies to total work Q. Numeric format compatibility
does not imply statement-semantic compatibility.

Receipt claim identifier: `suf-cma-total-work-pk32-decay-v1`.
The hash meter identifier is unchanged. Old receipts must be reverified against
the revised claim; changed protected hashes and the claim identifier distinguish
them. The renderer still binds all three declarations.

The objective is **sigma * hverify** for the hash-work profile, computed
with exact integer arithmetic in byte × verification-work units. The organizer-owned
`benchmark/scoring.json` uses schema `leansphincs-product-profile-v1` and profile
`signature-bytes-times-hash-work-v1`, bound by the harness manifest. There is no
bandwidth coefficient or entrant pricing. Retain both coordinates for Pareto
exploration. Historical additive profiles are rejected by the current loader;
the protected claim and verification meter identifiers are unchanged.

A diagnostic product score is emitted only after successful comparison and post-run
integrity checks. Every receipt is still `ranked: false`. The declarations-only
score helper also reports unverified/unranked status. The historical OTS additive Lean
helpers prove arithmetic properties, not algorithm certificates.

## Trust boundary, provenance and launch work

Source admission is flat, bounded and import-checked: 1,000 files, 4 MiB per file,
10 MiB total; no symlinks, dynamic elaborators, native_decide or build-time
execution. Protected sources and dependencies are read-only in candidate runs.
Private per-run projects, fresh candidate outputs, axiom checks, kernel checking,
admission locking, atomic receipts and integrity rechecks are described in
[HARNESS_SECURITY.md](HARNESS_SECURITY.md). None is an external audit.

- Lean: 4.31.0.
- VCVio: `cbd4144b51d92da00dd50f05e068b2348fa6e529`.
- Comparator: `777e7f56119efc0fac34003db4efe831e0b53723`.
- lean4export: `b18d673bd29b476466a51a3be1012df2ed322b10`.
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.
- Harness reference: proximity-prize `da60d54326afbe85d18a94d0e5c479a724e55ad7`.
- XMSS reference: `0e82ea922c570b8c4d706a06bc3dc7caf3b34ff0`.
- SPHINCS reference: `a1daec3b929d8963b4eee4f1e05985065a96de9d`.

The five positive/negative metric comparator canaries do not establish security.
WS5 needs mutation tests built from an accepted baseline; WS6 needs serialization,
game and cost transport, signing failure and same-scheme lifetime decay.
The full executable binding, 1.5 s signing / 60 s keygen / 64 KiB RAM gates,
persistent storage profile, execution cap and price calibration remain unfinished.
No fixed hash-unit-to-seconds conversion is asserted. Independent verifier
registration, audit, governance and promotion still precede launch.

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
