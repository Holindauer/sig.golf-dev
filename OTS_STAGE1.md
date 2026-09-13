# Experimental OTS foundations within the academic track

Status: experimental implementation, updated 2026-09-11. Not an open competition,
protected OTS security claim or accepted scheme. Stage 1 also covers few-time
components, encodings, authentication, composition and complete constructions.
This document describes only the current OTS research tools. Emile's construction
interface and the audited SPHINCS reference pin are unchanged.

## Current objective and experiment semantics

The rules use **c * signatureBytes + verificationWork**, with signing and keygen
subject to latency and absolute resource constraints. The positive rational c belongs to a calibrated
organizer profile. No official price has been selected and no scalar leaderboard
exists yet. Account normal latency targets are 1.5 s signing / 60 s keygen, each
with overrun probability <= 2^-60; RAM stays bounded by 64 KiB on every path.
Larger absolute timeouts, component allocations and full-program certificates
remain open. Abstract hash
counts do not certify seconds.

R9 requires finite budgets before an academic profile can rank entries. Raw
keygen/sign/verify query caps must also count repeated and empty-input queries
and prevent honest work from exhausting the security range. All setup and failed
retries count. Slow executions remain subject to absolute caps and the complete
security proof. Signing failure stays a separate 2^-128 gate; latency overrun
does not automatically cause failure. The current research declarations and
counting experiments do not provide those eligibility certificates.

`LeanSphincs/OTS/Score.lean` defines exact additive arithmetic, positivity and
monotonicity. `stage1RankKey price` and `stage2RankKey price` use that same
formula, not the same security game or metric profile. None of these arithmetic
lemmas certifies an algorithm's costs.

The experiment CLI defaults to the size/verification **Pareto frontier**.
An explicit `--bandwidth-price 1/8`, for example, explores a hypothetical
additive price using exact rationals; it does not set the competition price.
Signing work and its semantics remain required research inputs, with
`budget_certified: false`. No official scalar score is emitted without a price.

Historical decisions: the organizer approved the four-factor formula
`size * signing * verification * keygen^(1/4)` on September 9, then the
`size * verification` objective on September 10. Both are superseded by the
September 11 additive rule. `rankKey`, quarter-weight arithmetic and explicit
`selection="product"` helpers remain for reproducing those research snapshots;
they are not current stage rankers. The CLI no longer has a beta default.

Emile's polynomial-coding annex reinforces why we retain separate hash and
execution views. Field operations, codebook decoding and preprocessing must be
included in a full-program profile. Lower hash work is not necessarily lower
latency. See [POLYNOMIAL_CODING_REVIEW.md](POLYNOMIAL_CODING_REVIEW.md).

At fixed size and signing constraints, the conditional objective may be minimum
verification work. Chains are not presumed optimal; ROM-secure coded candidates
remain in scope. The current four-family experiment does not implement the
annex's complete signer/verifier, establish global optimality or certify budgets.

## Implemented foundations

- `LeanSphincs/OTS/Graph.lean`: finite acyclic-dependency predicate, distinct gate
  addresses, source/output vertices, structural reconstruction predicate and
  costs using the existing protected `hashWeight`. Each query returns two 128-bit
  vertices from the 256-bit oracle; using only one output does not reduce cost.
  A theorem bounds once-per-gate subset cost by total graph keygen cost.
- `LeanSphincsTest/OTSGraph.lean`: reconstruction/missing-input/cycle and input
  charging fixtures. The graph predicate does not enforce disclosure minimality,
  incomparability, or a byte-level verifier implementation. A reconstruction
  schedule still needs a root-correctness theorem against key generation.
- `LeanSphincs/OTS/Evaluate.lean`: actual `OracleComp HashSpec` evaluation of
  schedules, with fixed 16-byte little-endian addresses and values. Proved byte
  encoding injectivity, address separation, exact input length, gate query weight
  and worst-case weighted schedule query bound on every oracle response path.
  Missing inputs fail before hashing; repeats are charged repeatedly. For
  duplicate-free schedules, the operational budget equals the gate-subset cost
  and is at most graph keygen cost. This does not yet prove root correctness,
  randomized key generation or a complete OTS verifier bound including encoding.
- `LeanSphincs/OTS/Reconstruct.lean`: the actual oracle computation reconstructs
  the reference root when the disclosed values agree with an oracle-consistent
  assignment. This uses VCVio's `evalWithAnswerFn`, not a separate mock evaluator.
  Constructing the assignment from randomized keygen and transporting the result
  through the shared lazy ROM remain to prove.
- `LeanSphincs/OTS/Failure.lean`: real-valued adaptive survival-envelope theorem,
  an exception-aware variant for cached/bad steps, and a conservative exact
  retry bound at per-step success 2^-16. The actual signer must still establish
  the step premise and any exception allowance; these are not assumed facts.
- `scripts/ots_experiments.py`: exact integer polynomial counting for the four
  fixed graph shapes in *looking for the optimal hash-based one-time signature*.
  It searches reconstruction-cost layers and disclosure-size caps, selects the
  size/verification frontier by default, or the additive-minimizing pair at an
  explicit research price. Keygen is fixed per graph and the explicit
  signing metric is common across these codebooks. This is not exhaustive graph
  synthesis or a global optimality result.
- `scripts/check-ots-axioms.lean`: audit every declaration under `LeanSphincs.OTS`,
  including generated/private declarations, against the three standard axioms.
  Experimental modules are not imported by the protected MVP Target.

## Reproducible experiments

```sh
python3 scripts/ots_experiments.py --profile rom32-input64 \
  --signing-work 131072 --signing-kind expected-upper-bound
# Optional research price, not the competition profile:
python3 scripts/ots_experiments.py --profile rom32-input64 \
  --signing-work 131072 --signing-kind expected-upper-bound --bandwidth-price 1/8
python3 -m unittest discover -s tests -v
lake build LeanSphincsTest
lake env lean scripts/check-ots-axioms.lean
```

The example signing metric is hypothetical: 2^16 expected encoding queries times
two weighted units per query under the assumed layout. It is not a proved
signing certificate. The output explicitly says `ranked: false`,
`security_proved: false`, and `costs_certified: false`.

`paper` reproduces the note's 73/68/63/60 verification-cost minima under its own
oracle. The current `rom32-input64` profile assumes a fixed 16-byte unique gate
address encoded in every input, in addition to the 16-byte values. The oracle
output stays 32 bytes, while work is `ceil(inputBytes / 64)`. A four-input merge
or a 32-byte message plus 32-byte nonce costs two units with the address included.
A four-output expansion uses two separately addressed 32-byte-output queries.
Address serialization and separation are proved for the evaluator; reserved
encoding domains, construction-specific graph translation and simulation
equivalence still need proofs. Empty input costs zero hash-work units but still
counts as a security query; these graph queries all contain nonempty addresses.
The historical `rom32` profile keeps its old 32-byte input-unit costs for
reproduction only. JSON reports distinguish the meters; do not mix their scores.
These are candidate-layout choices, not a new competition oracle definition.

Under this layout, with 2^112 disclosures required and a cap of 128 disclosed
values, the historical product-selected points for the fixed graph shapes were:

| Fixed shape | Signature bytes | Keygen | Verification |
| --- | ---: | ---: | ---: |
| Chains | 1888 | 169 | 75 |
| Branching forest | 1648 | 201 | 96 |
| Pairwise shared seeds | 1744 | 220 | 101 |
| Four-way shared seeds | 1824 | 329 | 123 |

These rows are historical product-selected examples, not current additive
winners. Signing work was stipulated, not proved. These shapes no longer meet the note's keygen
budget of 168 under this meter. That budget is not adopted as a Stage 1 rule.
This reversal is not a general impossibility result for branching/shared seeds.

Size is a proposed canonical padded length: for each cost layer, retain eligible
disclosures in increasing size and a deterministic within-size order until there
are enough. Pad to the chosen cap and reject noncanonical padding. The counting
code does not implement the decoder or prove this SUF-preserving serialization.

## Next proof milestones, in order

1. Pin the first academic game, component budgets and price calibration.
   Account latency targets remain 1.5 s / 60 s with overrun probability <= 2^-60;
   the larger absolute caps still need calibration. No hash-unit-to-time conversion
   certifies these guarantees and no price is inferred from historical product winners.
2. Address serialization and actual oracle evaluation/metering are implemented.
   Reconstruction against an oracle-consistent reference is now proved. Next
   construct that reference from randomized keygen and transport through the ROM; instantiate each
   searched graph and bind its counting model to the actual implementation.
3. Formalize codebook counting/unranking, minimality and incomparability, including
   shared-seed disclosures. Prove canonical encoding and exact signature length.
4. Prove correctness and the fixed-message signing-failure certificate, plus the
   selected signing cost certificate. Include failed attempts and preprocessing.
5. With Emile, pin standalone chosen-message OTS versus the internal-root game.
   Prove strong one-time security under that game, with our raw whole-experiment
   query budget; combinatorial incomparability alone is not that theorem.
6. Use standard hybrid multi-instance reductions where applicable, recording
   their loss. Check the actual shared-ROM/domain-separation and key-derivation
   conditions and repeat-signing behavior in the consuming construction. Add a
   protected track claim/comparator and accepted baseline with mutation tests.
   Keep a direct-proof route beyond the templates.

No wallet feasibility, 127-bit theorem, certified candidate or optimal primitive
is inferred from these arithmetic and graph foundations.

## Worst-case failure probability

The organizer requested explicit treatment of worst-case probability. This does
not turn a conditional failure envelope into an actual signer certificate.
Signing is no longer a score factor. The normal latency targets now allow a
proved 2^-60 overrun probability per operation, while larger absolute caps
still bound worst-case work. The failure envelopes below concern exhaustion
at a retry limit; they are not already proofs of a runtime-tail guarantee.

The new proof bounds survival mass from a step inequality
`tail(n+1) <= tail(n)*(1-p)`. A success lower bound conditional on every surviving
history is sufficient, without independence. At `p = 2^-16`, blocks of 65536
attempts reduce the proved envelope by at least half. Hence:

| Illustrative target | Attempts | Worst-case encoding units at 3/attempt |
| --- | ---: | ---: |
| Single-request failure <= 2^-128 | 8,388,608 | 25,165,824 |
| Single-request failure <= 2^-256 | 16,777,216 | 50,331,648 |
| Per-request 2^-148, for a 2^20-request union bound of 2^-128 | 9,699,328 | 29,097,984 |

These are conservative sufficient caps **conditional on the step premise**, not
chosen protocol caps or completed availability certificates. The third row is a
composition illustration, not a change from the one-request OTS security game.
Only encoding queries are included in those work totals.

Freshness must be proved in the real game. Distinct signer nonces do not establish
that an adversary has never queried the corresponding inputs. A worst case over
adversary strategies with probability over the ROM is also different from
conditioning on every possible, including arbitrarily unlikely, oracle history.
Do not assert a uniform success probability for cached answers.

The exception-aware theorem instead accepts
`tail(n+1) <= tail(n)*(1-p) + bad(n)` and concludes the geometric bound plus
`sum bad(n)`. To certify a final 2^-128 failure gate, **both terms together** must
fit it. For example, allocating 2^-129 to each term suffices; neither exception
probability nor the uniform fresh-answer premise may be dropped.

Before eligibility, define the precise worst-case request/history scope, prove
the cache/freshness and retry behavior against the actual signer, and transport
the bound to the protected availability game. The current MVP fixed-message,
fresh-key availability clause has not been silently strengthened or replaced.

## Historical validation snapshots

Validation on 2026-09-09: 53 host tests passed; `lake build LeanSphincs
LeanSphincsTest` completed successfully (3305 jobs); both the protected and OTS
axiom audits admitted only standard axioms. No OTS security claim was added.

Quarter-weight/evaluator follow-up: 54 host tests pass; the complete library/test
build passes (3307 jobs), including byte injectivity, address separation,
missing-input rejection, both 128-bit output halves, repeated-gate charging and
the actual weighted-query theorem. Both axiom audits pass. The quarter-weight
CLI default is covered by a regression that also checks the unranked/unproved flags.

Reconstruction/failure follow-up: 54 host tests pass; full Lean build passes
(3311 jobs); both axiom audits pass. Lean fixtures cover correct reconstruction,
reversed invalid schedules, incorrect disclosures/reference assignments, 128/256-bit
failure envelopes, explicit exception accounting and single-request/lifetime arithmetic.
