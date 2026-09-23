# Hypertree optimization log

Research starts from organizer beta commit `7c2d18e4b797e81b312680e18ae119233d325729` and the published first-record candidate. The first two optimizations preserve all four images. The copy optimization changes only the verifier image; all routes preserve the reference scheme, signature format, and organizer definitions.

| Experiment | S | C | S × C | Result |
| --- | ---: | ---: | ---: | --- |
| Published baseline | 119632 | 5883520 | 703857264640 | Existing record |
| Account for WOTS checksum | 119632 | 5652800 | 676255769600 | Complete certificate checked locally |
| Account for short bottom layer | 119632 | 5617759 | 672063744688 | Complete certificate and full build checked locally |

The checksum ensures that the 46 base-8 digits sum to at least 14. Consequently the verifier performs at most 308 chain hashes per upper leaf, rather than the independent-chain bound of 322. The loop invariant tracks the cumulative hash cost, saving 1442 cycles per uniformly charged layer.

The bottom layer has one preimage leaf and skips WOTS encoding. Its complete layer cost is at most 288 cycles, versus 35329 for an upper layer. With the verifier prefix and footer, the final bound is `145 + 288 + 159 * 35329 + 15 = 5617759`.

Validation commands:

```sh
lake build SigGolf SigGolfTests SigGolfCandidate
python3 examples/hypertree/check.py
python3 verifier/check_submission.py ../sig.golf-submissions/submission
lake env lean ../sig.golf-submissions/submission/Solution.lean
```

The Python comparison uses SHA-256 only as a test oracle. Its sample verifier uses 3306952 cycles; this measurement is not the universal bound. The Lean certificate and axiom guards establish the proof obligations. Local checks are distinct from an organizer judging result.

Next experiments should inspect the 103-cycle hash-chain step for redundant memory operations and consider signature compression through `expand`. Any image or format change requires regenerating the images and re-establishing their functional, termination, resource, and security proofs. Keep the best passing certificate as the incumbent, and reject measurements without a corresponding valid certificate.

## Unrolled chain copies

Local checkout: `research-copy16`, based on development commit `e608fbb`. Only the two hot 16-byte copy loops are unrolled. Each executes 10 instructions instead of 17, retains its 11-word footprint, and preserves the entire final machine state. The new Lean module proves both exact-state replacements, instruction traces, memory frames, and the 76-cycle chain core. Each full iteration is 89 cycles.

The resulting certificate claims S = W = 119632, C = 4932151, score = 590043088432. The bound is `145 + 288 + 159 * 31017 + 15`. This is 12.20% below the pending candidate's score. The SHA-256 sample uses 2935434 cycles; sample hash counts and outputs are unchanged. Sixty differential copy-state cases, including overlapping buffers, pass.

The local submission bundle is `../research-copy16-submission`. Keep it local until PR #2's exact head `30df6732c6ab44354ff5f22108d9a49b6ae59aa7` passes official validation. Consult `../autoresearch-state.json` for final validation status and the local commit.

Next route: simplify the 42-instruction chain hash header. First try reusing address registers and base-relative loads/stores while preserving the exact final state and instruction footprint. This avoids requiring an invariant about an earlier iteration. Hoisting invariant fields out of the loop offers larger savings, but requires proving that every entry and intervening call preserves those fields. Keep each new experiment separate from the checked candidate.

## Shared-base chain header

Checkout: `research-header`, based on `f4e8014`. The verifier header reuses one base register for its loads and stores, executes 24 instructions instead of 42, and retains its 42-word footprint using a jump over padding. Including HASH argument setup, `FastChainHeader.block` proves 30 ordinary steps reach exactly `KeygenChainHeader.state` for every initial machine state. `FastHeaderChain.chain_compute` uses this to prove a 58-cycle core and 71-cycle complete iteration.

Proposed S = W = 119632, C = 4050655, score = 484587958960. Full cost: `145 + 288 + 159 * 25473 + 15`. The sample uses 2457768 cycles with unchanged outputs/hash counts; tampered signature, randomizer, and message rejection tests pass. A separate local bundle is at `../research-header-submission`. Final validation status is in `../autoresearch-state.json`.

PR #2 officially passed at 2026-09-23T08:23:11Z under contract `7c2d18e4b797e81b312680e18ae119233d325729`; exact head `30df6732c6ab44354ff5f22108d9a49b6ae59aa7` is a published record. It was closed after validation to submit the next beta candidate as PR #3, exact head `24a6554bd4cc77ceea4fc8f27987375443c0a0e1`. Hold new submissions until PR #3 passes official validation.

A follow-on differential probe at `../research/combined_address_probe.py` tests 30 states per fragment: full header plus HASH argument setup 48 → 27 instructions, and each unrolled copy 10 → 9 instructions. Compared with this header candidate, that saves another five cycles per chain hash. The probe is not an integrated program; its corresponding standalone Lean proofs are described below. Next: create an isolated checkout from this completed candidate and prove those three exact-state replacements.

Validation caught an unintended application of the header optimization at the bottom-leaf hash. The generator is now restricted to the `chain_step`/`chain_end` region; the corrected image restores the original bottom path. Its sample costs 2457768 cycles. A decidability elaboration issue was resolved by using the header Code instance rather than unfolding its whole conjunction.

The next-route module `../research/AddressReuseProof.lean` now passes Lean standalone against the copy16 baseline: all three exact-state equivalences and ordinary execution traces (27 header/setup steps, 9 steps per copy) are proved with permitted-axiom guards. It still needs integration into a fresh candidate image and propagation through the full certificate.

The complete header certificate and permitted-axiom guards pass. The exported local `Solution.lean` is checked separately; final broad-build status and exact commit are recorded in the autoresearch state.

## Reuse addresses in chain copies and HASH argument setup

Checkout `research-address-reuse`, based on `162e3f7`. The full header/setup now executes 27 instructions, and each copy executes nine. The program keeps all static instruction addresses and complete final states unchanged. The chain core uses 46 steps/53 cycles; the full iteration uses 59 steps/66 cycles.

Proposed C = 3805795, score = 455294867440, with unchanged S = W = 119632. Bound: `145 + 288 + 159 * 23933 + 15`. Reference comparisons and malformed-input rejection pass; sample verification costs 2325083 cycles with unchanged hash counts. The local bundle is `../research-address-reuse-submission`. Final full-build validation status is recorded in `../autoresearch-state.json`.

Next route: `../research/FastIncrement.lean` proves a six-step counter increment matches the original eight-step increment, including its backward jump and complete state. Integrate the shorter fragment followed by two unreachable padding words in a new isolated checkout; preserve the checked candidate and pending PR until official validation.

The complete address-reuse certificate, permitted-axiom guards, and exported `Solution.lean` all passed. Organizer modules and pinned dependencies are unchanged. Final broad-build status and commit are saved in the autoresearch state.

## Counter-address reuse

Checkout `research-increment`, based on `644dd82`. Reuse x28 for the step-counter store, move the backward jump two instructions earlier, and leave two unreachable padding words. `FastIncrement.block` proves six steps reach exactly the old increment state. Full chain iteration: 57 steps/64 cycles.

Proposed C = 3707851, score = 443577630832; S = W = 119632. Bound: `145 + 288 + 159 * 23317 + 15`. Reference comparisons and rejection cases pass; sample verification costs 2272009 cycles with unchanged hash counts. Final validation and exact commit are in `../autoresearch-state.json`.

Next route: `../research/Copy6.lean` proves six-step copies satisfy the exact memory, stack, return-address, and PC specifications required by the chain core. It intentionally does not claim preservation of unused temporary registers. Prototype script: `../research/copy6_probe.py`. Integrate in another isolated checkout and re-establish the complete certificate before claiming a universal improvement.

The six-step-copy prototype passes full reference and malformed-input rejection tests at 2112787 sample verification cycles, with unchanged hash counts. The smaller copy execution/specification theorems and axiom guards pass standalone; a full integrated certificate remains necessary.

The complete counter-update certificate, permitted-axiom guards, source policy, and exported `Solution.lean` pass. Organizer definitions and pinned dependencies are unchanged. Full-build result and local commit are recorded in the autoresearch state.

## Six-step chain copies

Checkout `research-copy6`, based on `e160eee`. Replace both chain copies with a shared-base load/store fragment and a jump over unused padding. Each executes six steps instead of nine. The proofs preserve the required memory frame, return address, stack pointer, and following PC; temporary registers need not match. The full chain iteration uses 51 steps/58 cycles.

Proposed C = 3414019, score = 408425921008, S = W = 119632. Bound: `145 + 288 + 159 * 21469 + 15`. Reference comparisons and malformed-input rejection pass; sample verification costs 2112787 cycles with unchanged hash counts. Final validation and commit are in `../autoresearch-state.json`.

Next route: `../research/FusedPrepare.lean` proves a combined copy/header block executes 31 ordinary steps and reaches exactly the prior prepared state. This removes one jump and one repeated base-address load, saving two cycles per chain hash. Prototype: `../research/fused_prepare_probe.py`. Integration and a complete certificate are still required.

The complete six-step-copy certificate, permitted-axiom guards, source policy, and exported Solution.lean passed. The combined-block prototype also passes reference and malformed-input rejection tests at 2059713 sample cycles. Full broad-build status and candidate commit are in the autoresearch state.

## Combined input copy and hash header

Checkout `research-fused`, based on `7218095`. Combine the input copy and header setup into 31 instructions across the original 59-word footprint. Remove a repeated base load and one jump; the HASH instruction stays at the same address. `FusedPrepare.block` reaches exactly the original prepared state. The core uses 38 steps/45 cycles and the full iteration 49 steps/56 cycles.

Proposed C = 3316075, score = 396708684400, S = W = 119632. Bound: `145 + 288 + 159 * 20853 + 15`. Reference and rejection tests pass at 2059713 sample cycles with unchanged hash counts. Final validation/commit are in the autoresearch state.

Next route: `../research/FusedFinish.lean` proves a ten-step output-copy/counter-update block reaches exactly the old final state. Prototype: `../research/fused_finish_probe.py`. It preserves the 19-word footprint and saves another two cycles per chain hash. A full integrated certificate is still required.

The complete combined-preparation certificate, axiom guards, exported Solution.lean, and source policy pass. The output-copy/counter prototype also passes all reference/rejection tests at 2006639 sample cycles. Final broad-build result and commit are checkpointed in autoresearch state.

## Combined output copy and counter update

Checkout `research-finish`, based on `5f5d721`. The combined ten-step ending preserves the final state of the previous copy/increment pair across its original 19-word footprint. The chain core theorem includes the increment in its trace; the full iteration uses 47 steps/54 cycles.

Proposed C = 3218131, score = 384991447792, S = W = 119632. Bound: `145 + 288 + 159 * 20237 + 15`. Reference/rejection tests and final validation are recorded in autoresearch state.

Next route: 152-level hypertree. The standalone shared-budget and index-monitor proofs pass with permitted axiom guards; the prototype reference/bytecode tests pass at 113616 signature bytes and 1891993 sample cycles. Full adaptation of reference, bytecode, security, termination and resource proofs remains. See `../research/height152-notes.md`; do not treat the prototype as certified.

The complete combined-ending certificate and axiom guards, exported Solution.lean, source policy and reference/rejection checks passed. Organizer definitions and pinned dependencies are unchanged. Broad-build status and exact commit are in autoresearch state.


## 152-level research checkpoint (2026-09-23)

PR6 remains fixed at f95c734241fd45a4b640a45338dceb618f3222e9. This isolated checkout is an incomplete research branch, not a submission candidate.

The adapted SecurityIndexMonitor, SecurityIndexTrace, SecurityIndexProgram and SecuritySharedBudget target built successfully (2760 jobs), including permitted-axiom guards. Reference.correct also built for height152 (2704 jobs). The earlier Python prototype passes reference/rejection tests at113616 bytes. These are component proofs only; dependent security and bytecode modules still require adaptation.

Next executable step: inspect Signature.lean and SecurityPath.lean to adapt the compact signature's151 upper layers, then adapt SecurityRandomOracle's152-bit output and104-bit extraction complement. Build those targets before propagating changes through graph and common-monitor modules. Review each numeric occurrence; PC offsets must stay unchanged. The old auxiliary SecurityAccounting.combine_query_classes theorem has a different coarse bound and cannot simply replace160 with152; preserve or separately generalize it only if actually required. Keep organizer lambda127/lifetime2^24 unchanged. Finally regenerate bytecode from the saved height152 prototype, update refinements and resource proofs, and complete the entire certificate before claiming a new bound.


## 152-level candidate validation complete

The complete certificate and permitted-axiom guards pass at S=W=113616, C=3056235, score 347237195760. The bound is 145+288+151*20237+15. Full build passed 3053 jobs, exported Solution.lean compiled, source policy passed, bundle sources match, and independent reference/rejection tests passed. Sample verification uses 1891993 cycles; this is distinct from the universal bound. Organizer definitions and pinned dependencies remain unchanged.

The prior full-build attempt found stale memory-end and expansion-cycle literals; those were repaired and the final full build passed. PR6 at f95c734241fd45a4b640a45338dceb618f3222e9 is still pending. Preserve this ready local candidate and do not submit until that exact head is officially recorded. Next local route: reuse the STEP address on the chain backedge; see research/chain-check-reuse-notes.md outside this checkout.


## Active route: STEP address reuse

This isolated checkout starts at f0e93079e0c0acbfe5ed99a0411bda980e6cb435, the fully validated 152-level candidate. Keep that candidate and its export unchanged. PR6 remains pending at f95c734241fd45a4b640a45338dceb618f3222e9.

Standalone research/CheckReuse.lean proves exact shortened-check equivalence when x28=STEP, and proves FusedFinish supplies that register value. The prototype in research/check-reuse-probe passes all reference/rejection checks at 1842097 sample verification cycles (previously 1891993). No universal bound has been certified for this new route.

Next executable step: copy the prototype build.py here and regenerate Images.lean. Adapt FusedFinish's backedge from -296 to -288 and its increment-equivalence offset from -332 to -324. Prove the three-instruction check starting at0x14f4, retaining the first-entry two-instruction setup at0x14ec. Strengthen the repeated-loop invariant with x28=STEP and update VerifyChainLoop accounting, followed by all affected resource bounds and the complete certificate. Source prototype/proof paths and exact validation logs are saved in autoresearch-state.json outside this checkout.


## STEP-address reuse validation complete

The complete certificate passes at S=W=113616, C=2963219, score 336669089904. Full build passed 3054 jobs; permitted-axiom guards, source policy, exported Solution.lean, exact bundle equality, and reference/rejection tests passed. The sample uses 1842097 verification cycles. Only the verifier image changes. The recurrent step is 45 ordinary instructions and 52 cycles; each full chain pays its two setup instructions once, giving 52*remaining+5 cycles. The universal bound is 145+288+151*19621+15.

A shared ChainData.check lemma initially affected the signer proof. The original lemma is restored, and the verifier uses ChainData.shortCheck separately. The final full build passed after that repair. PR7 remains the only pending submission; preserve its exact head c16dcb4a90b16585bdc3c72e9da1d95fae87530c.

Next route: remove the redundant initial LUI from FusedPrepare and FusedFinish using their established x28 values. The separate prototype passes reference/rejection tests at 1792201 sample cycles. ReuseChainBases.finish_equiv passes; its first monolithic prepare_equiv proof hit kernel recursion depth, so a component-wise equality proof is being tried. Read autoresearch-state.json for its exact session/log and avoid repeating the failed proof.


## Active route: reuse both chain base registers

This checkout starts at54d8813d4fa84904aadc79fbe5d21ed161f29f1c. The ready STEP-check candidate is preserved separately. The next prototype removes the initial LUI in prepare (x28 already STEP) and finish (x28 already HASH+24), adjusts relative offsets and the jumps, and leaves static footprints unchanged. Prototype/reference tests pass at1792201 sample cycles.

First resume the component-wise prepare proof session73752, log /private/tmp/siggolf-reuse-chain-bases-split-proof.log, source research/ReuseChainBases.lean outside this checkout. The previous monolithic proof failed kernel recursion; do not count it as passed. Once the equivalence proof works, integrate research/reuse-chain-bases-probe/build.py, prove actual30/9-instruction executions and required register invariants, and complete every certificate/export check before publication. PR7 remains fixed until official validation.

The field-wise equality attempt has also finished with kernel deep recursion at50000. Session73752 exited1. Next split the preparation into short instruction fragments with separately checked equivalences; adding state_ext alone was insufficient. Both failures are saved in research/validation. This is unfinished local proof development, not a submission blocker.


## Both chain base registers: validation complete

The complete certificate, all permitted-axiom guards, full 3057-job build, exported Solution.lean, source policy, exact export-source comparison and reference/rejection checks pass. S=W=113616, C=2870203, score 326100984048. The sample verification cost is 1792201 cycles. The exact full bound is 145+288+151*19005+15.

The preparation equivalence was proved by composing ten small instruction-fragment relations; the earlier monolithic and field-wise giant proofs hit kernel recursion and are not used. ReusePrepare and ReuseFinish prove 30/9 executed instructions under explicit base-register premises. The iteration now takes 43 instructions/50 cycles. Organizer definitions and pinned dependencies remain unchanged.

Next route: cached chain hash headers. Its separate prototype/reference tests pass at 1509766 sample cycles; CachedHeaderArithmetic.lean proves the modular step-word increment and finishing-block header preservation with permitted axioms. Full loop invariants and certificate remain. See research/cached-header-notes.md and autoresearch-state.json outside this checkout. Keep PR7 exact head fixed pending official publication.


## Active route: cached chain headers

This isolated checkout starts at085c5761aa15eb33c19197b2e451baca27b53821. PR8 remains fixed atbf26d2b4920f61d6291d67107c47af50f3859e59. Read research/cached-header-notes.md and research/CachedHeaderArithmetic.lean outside this checkout. The separate prototype passes reference/rejection checks at1509766 sample cycles, and the arithmetic/preservation component proofs pass. Full execution and security/resource certificate integration remains.

Next executable step: integrate research/cached-header-probe/build.py and regenerate the image. Define the preceding-step header invariant; prove the15-instruction recurrent preparation and the distinct initial/recurrent checks. Preserve exact register/frame facts. Derive the one-time15-cycle surcharge per nonempty chain before adjusting leaf and universal bounds. The prospective2276773-cycle total is not yet certified.

### Cached-header proof checkpoint (2026-09-23 heartbeat 11:10 UTC)

Added CachedPrepare, CachedCheck, CachedFusedFinish, CachedFinish, CachedInvariant and CachedChain. Component build succeeds (2745 jobs) with permitted-axiom guards. The 15-instruction preparation has full memory equivalence to the full header builder under Ready; register arguments, PC, stack and frame are proved. Header Current/Ready invariants are established by the initial full builder and preserved through recurrent prepare, HASH, finish and check. CachedChain.chain_compute proves a 25-instruction / 32-cycle / one-hash computation, reference digest correctness, frame/stack preservation, and Ready on exit. The three-instruction check yields the planned35-cycle recurrent iteration. The standalone research/CachedPrototypeCode.lean compiles and certifies all four relevant blocks against the actual tested prototype image, including offsets0x1500/0x1578/0x1584/0x15f0.

These are component proofs, not a new full submission certificate: Images.lean and the existing candidate remain unchanged. Next implement an initial-chain compute using full ReusePrepare with CachedFinish, establish Ready after its first hash, then adapt VerifyChainStep and VerifyChainLoop to split the first50-cycle iteration from recurrent35-cycle iterations. Integrate the prototype image only with these code/proof updates, propagate35*n+20 bounds through leaf/layer/certificate, and perform full validation. Proposed2276773 bound remains uncertified. PR8 exact bf26d2b4920f61d6291d67107c47af50f3859e59 remains pending; no new submission was made.

Failed proof tactic recorded: raw unfolding all MachineState field operations in the15-instruction mem lemma consumed22GB after~80s and was stopped. Existing getReg_setReg_eq/ne and memory simp lemmas solve this in seconds. BitVec numeral normalization can prevent rw matching; congrArg over Word addition followed by simpa solved the step increment invariant. Do not repeat raw full-state expansion.

### Cached-header integration validated (2026-09-23)

PR8 bf26d2b4920f61d6291d67107c47af50f3859e59 officially landed at2026-09-23T11:28:14Z under contract7c2d18e4b797e81b312680e18ae119233d325729, matching S=W113616,C2870203,score326100984048. It is the incumbent.

Integrated InitialCachedChain, CachedChainStep and CachedChainLoop. Empty chains cost5cycles; nonempty chains cost35*n+20. The universal leaf bound is13724 and upper-layer bound15075. Final C=145+288+151*15075+15=2276773, S=W113616, score258677841168. Complete3065-job organizer/candidate build passes, including security/resource certificate and permitted-axiom guards. Exported Solution.lean compiles, source policy passes356files2411453bytes, exact352Lean-file bundle comparison passes, protected organizer/dependency diff is empty, and reference/rejection tests pass (sample1509766 verificationcycles). Durable evidence is in ../research/validation/siggolf-cached-*. The first full build found a shared exact-hash-count proof still using old trace costs; it was repaired without changing the count, and the complete rebuild passed.

Next route: retain2^32 in x13 across chain hashes. Prototype research/cached-constant-probe passes reference/rejection tests at1484346samplecycles. research/CachedConstantPreservation.lean proves installation and check/HASH/finish preservation with permitted axioms. No integrated certificate for that route yet. Start a separate beta clone from this validated candidate; use research/cached-constant-notes.md. Keep the new submitted SHA fixed until an exact matching official record appears.

### Active next route: cached constant

PR9 submitted; exact candidate and validation are recorded in ../autoresearch-state.json. Continue from research/cached-constant-notes.md and CachedConstantPreservation.lean. This checkout is isolated on beta; origin is local and must not be pushed.

### Constant-register candidate ready locally (2026-09-23)

Retain2^32 in x13 across the chain. Initial preparation32instructions, recurrent preparation13; first iteration52cycles, recurrent33. The complete loop handles zero hashes in5cycles and nonempty chains in33*n+24. Full leaf bound13292, upper-layer14643, final C=145+288+151*14643+15=2211541. S=W113616; score251266442256.

All3068 build jobs pass, including the complete certificate, organizer tests, resource checkpoints and permitted-axiom guards. Solution.lean compiles; source policy367files2491500bytes and exact363Lean-file comparison pass; protected definitions/dependencies unchanged. Reference/rejection tests pass at1484346sample verificationcycles. Bundle research-cached-constant-submission; durable validation logs research/validation/siggolf-constant-*. This candidate is READY LOCALLY, not officially submitted or accepted. PR9 a63d249a1fc5d642ab9ecb9957b4c96cb6330d8b remains pending and its head is unchanged.

Next route tested separately: write HASH output over its input digest at0x80020, omit repeated digest copies, restoreVALUE only on nonempty chain exit. Reference/rejection tests pass at1339833samplecycles. research/InplaceHash.lean proves exact answer words, header preservation and8-cycle HASH trace with permitted axioms. Read research/inplace-chain-notes.md; planning C1901991 is not yet certified. Continue this route in an isolated beta clone while PR9 is pending. Once PR9 lands, submit the best fully validated ready improvement, preserving accepted SHAs and at most one unvalidated PR.
