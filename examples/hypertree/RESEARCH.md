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

### Active in-place chain route

This isolated beta checkout starts from the fully validated constant-register candidate. PR9 remains pending. See research/inplace-chain-notes.md and research/InplaceHash.lean. Origin is local; never push it.

### In-place chain component checkpoint (2026-09-23)

PR9 a63d249a1fc5d642ab9ecb9957b4c96cb6330d8b officially landed at12:10:19Z with S=W113616,C2276773,score258677841168 under contract7c2d18e4b797e81b312680e18ae119233d325729. Submitted the fully validated constant-register candidate as PR10, exact SHA b447a456397dd109dcb609e150522fbff411b372, S=W113616,C2211541,score251266442256. Preserve that head pending official publication.

New in-place component proofs pass (2750-job build with axiom guards): InplacePrepare9instructions, InplaceFinish5, InplaceRestore5, InplaceCheck3. InplaceInvariant proves prepare/current-header, HASH preservation, finish/next-header, check preservation and final digest restoration. InplaceHash proves overlapping-input/output trace8cycles, exact output words, reference chain-hash answer words and frame. InplacePrepare.header_memory_equiv connects its state to the existing full header semantics with the digest already inHASH+32. Standalone research/InplacePrototypeCode.lean checks all four proved code blocks against actual prototype instructions at0x1580,0x158c,0x15f0,0x1604. Images.lean and the current submission remain unchanged; this is not a full candidate certificate.

Next executable step: implement/prove32-instruction InplaceInitialPrepare by adapting ConstantInitialPrepare with x12 destination0x80020, preserving the x13 setup. Then assemble recurrent9+HASH+5 core from InplacePrepare/InplaceHash/InplaceFinish with value carried atHASH+32 instead ofVALUE. Introduce BufferedChainData or equivalent invariant, use InplaceRestore only for the nonempty exit, and keep zero-length initial exit untouched. Reprove first48cycle and recurrent25cycle traces, chain bound25*n+33, leaf/layer/certificate bounds and full validation. Proposed C1901991 remains uncertified. Continue from research/inplace-chain-notes.md and the checked component modules. Do not push this checkout's local origin.

### In-place chain digest integration

The first preparation establishes a buffered digest at HASH+32; recurrent HASH writes back there. Initial and recurrent steps are proved at48 and25cycles; nonempty chains restore VALUE on exit, while zero-length chains leave VALUE untouched. The complete certificate compiles atS=W113616,C1901991,score216096609456. The full build passed all3074jobs, including the unchanged keygen resource checkpoint. Exported Solution.lean, exact375-file Lean bundle, source policy379files2571115bytes, protected-definition comparison and independent reference/rejection checks pass. Sample verifier1339833cycles1149766instructions25253hashcalls26915compressions. Pending PR10 remains b447a456397dd109dcb609e150522fbff411b372; do not submit another candidate until exact official publication.

Next route: persistent HASH argument registers. Independent prototype passes at1283346samplecycles. research/PersistentHashArgs.lean proves exact preparation-state equivalence under x11=384,x12=0x80020,x5=1, plus check/HASH/finish preservation with permitted axioms. Integrate in a separate beta clone, retaining these invariants through the buffered loop. See research/persistent-hash-args-notes.md for exact executable steps and prospective (uncertified) C1783305. Never push the local research origin.

### Persistent HASH argument registers

The recurrent preparation now reuses x11=384,x12=HASH+32,x5=1, which are installed by the initial preparation and preserved by HASH, check and finish. Exact six-instruction preparation equivalence, ordinary execution, preserved invariants, and complete chain-loop proofs pass. Recurrent step22cycles, nonempty chain22*n+36, emptychain5. Complete certificate and exported Solution.lean compile atS=W113616,C1783305,score202611980880. Reference/rejection tests pass at1283346samplecycles1093279instructions25253hashcalls26915compressions. Source policy380files2578080bytes, exact376Leanfile bundle and organizer-file comparison pass. The full build passed all3075jobs, including the final keygen resource checkpoint.

The first full build encountered ENOSPC. Removed only regenerable .lake/build caches from eleven completed research routes, preserving all source/Git history/packages/submission bundles/logs and freeing9.2GB. Re-ran reference tests and full build.

PR10 exactb447a456397dd109dcb609e150522fbff411b372 officially landed under contract7c2d18e4b797e81b312680e18ae119233d325729 at2026-09-23T12:48:47Z. Submit this stronger combined in-place/persistent-argument candidate when full validation finishes.

Next route: keep chain counter in x6. Prototype/reference/rejection tests pass at1233450samplecycles. research/RegisterCounter.lean proves exact finish/check equivalence and initial/preparation/HASH/finish counter invariants with permitted axioms. research/register-counter-notes.md records entry addresses, actual instruction lengths, planning bounds and executable next steps. No full certificate for that route.

### Retain the chain counter in x6

The initial check loads x6 from STEP. Initial/recurrent preparation and HASH preserve both; a four-instruction finishing block increments x6 and writes STEP. The recurrent check now uses two instructions. CounterArgs relocates preparation to0x1588 while HASH remains0x15ec; a padding word preserves restore0x1604. Proved initial40instructions47cycles, recurrent13instructions20cycles, nonempty20*n+36 and empty5. The universal bound is1690289 atS=W113616, score192043875024; full3080-job build, certificate/permitted-axiom guards and exported Solution.lean compilation all pass. Independent bytecode/reference/rejection checks pass at1233450samplecycles1043383instructions25253hashcalls26915compressions. Source policy388files2623694bytes, exact384Leanfile bundle and protected-definition comparison pass.

Proof development: implicit definitional comparison across setPC exhausted200000heartbeats; increasing the limit caused slow elaboration and was stopped. Explicit getReg_setPC/getMem_setPC framing reduced the recurrent-data proof to1.8seconds and both entry proofs pass. Do not repeat the implicit comparison approach.

PR11 remains pending at exact5bbb78dd6ad273039482af1a255643a06bdd7aec. Preserve its head; do not submit until its exact official record is published. Next route: persist x7=7 from the initial check, reducing recurrence to one branch. Separate reference tests pass at1208502samplecycles, with branch, initialization, and preservation lemmas checked in research/PersistentLimit.lean. Follow research/persistent-limit-notes.md for integration and prospective (uncertified) C1643781.

### Persist the chain limit in x7

The initial check installs7 in x7; all chain preparation/HASH/finish blocks preserve it. The recurrent check is one BEQ, with preparation at0x1584 and HASH still0x15ec. Proved recurrent12instructions19cycles, nonempty19*n+36 and empty5. The complete certificate and exported Solution.lean compile atS=W113616,C1643781,score186759822096; the full3081-job build passed, including the final keygen resource checkpoint. Source policy389files2628644bytes, exact385Leanfiles and unchanged organizer/dependency checks pass. Integrated reference/rejection checks pass at1208502samplecycles1018435instructions25253hashcalls26915compressions.

PR11 officially landed at2026-09-23T13:26:23Z under contract7c2d18e4b797e81b312680e18ae119233d325729 with exact5bbb78dd6ad273039482af1a255643a06bdd7aec. Submitted the already validated counter route as PR12, exacte04ef8d0a63b67de9c356ae90865413ff1f32d84, S=W113616,C1690289,score192043875024. Its head must stay fixed until exact official publication.

Next independent route keeps x28 at STEP throughout chain hashing. Prototype/reference/rejection tests pass at1158606samplecycles, and research/PersistentStepBase.lean proves exact initial/recurrent/finish state equivalences with permitted-axiom guards. Initial proof uses a shared24-instruction prefix and shorter tail. See research/persistent-step-base-notes.md for exact executable proof steps, fixed addresses and prospective (uncertified) C1550765.

## 2026-09-25: migration to organizer contract be68468 (in progress)

PR12 authoritative exact SHA is
`e04ef8d0a63b67de9c356ae90865413ff1f32d84`, official score192043875024,
S=W113616,C1690289 under contract7c2d18e. Preserved accepted source unchanged.
The x7 checkpoint9f16f60 is validated ONLY against that old contract; do not submit.

This isolated beta checkout merges organizer be68468c347b0aeb887b1900abcf4214e76c1951
(the deployed contract revision reported by upstream beta c6b2462). Protected
SigGolf and dependency files match organizer exactly. Candidate merge conflicts
resolved for current152-level source; this does NOT certify the new security bound.
LIFETIME is now2^32, so the old152-bit index collision argument must change;
restore160 levels using height-change commits36bf323/f0e9307 as a precise guide.
Do not change organizer definitions or relax the security statement.

Completed migration components:
- Executes.ordinary charges instructionCycles; Executes.sound passes axiom guard.
- OrdinarySteps.step now requires unitCost: instructionCycles instruction=1.
- Trace.ordinary charges instructionCycles; OrdinarySteps.trace uses unitCost.
- Trace.sound and composition compile with permitted axioms.
- lake build SigGolfCandidate.Execution:2702jobs pass.
- lake build SigGolfCandidate.Hypertree.KeygenTrace:2703jobs pass.
Logs ../research/validation/siggolf-contract-{execution,trace}.log.

Next executable work: migrate OrdinarySteps.step callers with explicit unit-cost
proofs (or a sound autoParam for concrete unit-cost instructions), then HASH
setup bytecode/register values from bits to bytes, hashInput proofs preserving
exact oracle queries. Restore160 levels and recalculate every bound using new
instruction prices plus ceil(W/256) witness cycles. Update independent Python
interpreter/reference tests to the official semantics. Add six-offset claim
layout and exported layout_offsets. Full certificate, exports, source policy,
protected comparison and reference/rejection tests must pass before submitting.
Current claim/C/images are stale; there is no newly certified candidate here.

Additional optimization preserved in ../research-persistent-step-base at91adbc2:
all2772jobs pass for STEP-base initial/core/recurrent/loop components under OLD
contract; recurrent17cycles, nonempty17*n+36. Integrate after baseline migration.
Never push this checkout's origin (it points to local research-persistent-limit).

### 2026-09-25T22:00 continuation

Unit-price migration now passes KeygenTreeControl (2707jobs): OrdinarySteps
constructor stepCost retains an explicit price proof; compatibility theorem step
uses `by rfl` default proof for concrete unit-cost instruction constructors.
`by decide` was rejected for symbolic ADDI/JAL operands; definitional reduction
solves this without an axiom or weakening. OrdinarySteps induction cases must
use stepCost and carry unitCost. KeygenBlocks HASH helpers now take byte counts,
require whole-word alignment, and charge compressions(8*byteCount).

Independent prototype: ../research/contract-byte-probe/{build.py,check.py}.
Restores160levels, HASH byte lengths, derives public key from secret key at start
of signing (new sign input no longer includes pk), resets scratch state, then
signs. Caller-supplied cache remains unused. All keygen/sign/expand/verify
reference comparisons and malformed signature/randomizer/message checks pass.
Signature119632bytes; sample verify1280208executioncycles+468witnesscycles=
1280676chargedcycles. Sign uses121769compressions including761for key derivation,
below131072 in this test. These are SAMPLE measurements, not a certificate.
Prototype only uses non-M ordinary instructions; unsupported M instructions are
rejected by its interpreter rather than incorrectly priced.
Log ../research/validation/siggolf-contract-probe.log; measured-run.json inprobe.

Next: migrate HASH setup/caller proof literals from bits to bytes while keeping
reference Query bit lengths unchanged. Serialization input assumptions change
to byte counts. Import prototype changes into actual candidate only along with
all corresponding image-address, sign-loader,160-level security and cycle proofs.
Sign public-key recomputation is essential; merely deleting pk from loader is
incorrect for our existing candidate. No submission prepared or sent this wake.

### 2026-09-25T22:05 byte-HASH integration

Migrated explicit x11 HASH-length proof constants and instruction definitions
from bits to bytes (35 modules initially), regenerated all four images at the
same instruction counts572/796/15/578. Leaf HASH length keeps its two-instruction
setup as LUI x11,0; ADDI x11,x11,768 to preserve every code address. Image delta
check confirms only length-setup instructions differ:7keygen,9sign,0expand,6verify;
evidence ../research/validation/siggolf-contract-image-delta.json.

KeygenDomain dependency build passes2726jobs, including exact node/chain/secret
oracle query proofs, serialization, real randomizer HASH and copy proofs.
SignIndex and KeygenLeafQuery also compiled in the broader component run.
Fixed OrdinarySteps deterministic proof induction to retain stepCost premise.
FastCopy16 embeds an experimental image used in proof dependencies; migrated
its raw HASH immediates too (its old image failed the updated exact Code check).

Still incomplete:160-level restoration and sign public-key derivation are only
in the separately tested prototype. Actual candidate remains152levels and its
signer expects pk; do not submit. Next after HASH components: build retained-limit
loop/certificate to find remaining HASH constants and proof API changes, then
restore160levels and signing prelude with their bounds. Preserve acceptedPR12.

Final component result: KeygenLeafQuery, PersistentLimit and SignIndex build
PASS2756jobs with their axiom guards (siggolf-contract-hash-components3.log).
No outstanding build process. Full certificate remains unvalidated as above.

### 2026-09-25T22:11 full-certificate dependency audit

Full certificate build reached3071jobs and exposed four failing roots:
Loader (obsolete public-key sign input), ResourceHash (old bit lengths),
SecurityBytecodePrograms (signingOracle API), SecurityIndexMonitor (152-bit
index insufficient for new2^32 lifetime). Full log:
../research/validation/siggolf-contract-certificate-first.log.

Repaired and validated Loader, ResourceRun, SecurityBytecodePrograms together:
PASS2759jobs, log siggolf-contract-loader-resource2.log. Loader secret-key/message
lemmas use actual3-input signer. Removed obsolete sign_publicKey loader lemma;
it cannot be true under current inputs. Callers requiring pk must receive a
real public-key derivation trace. No artificial replacement premise or axiom.
ResourceHash enforces byte-length alignment and compressions(8*bytes);
ResourceRun charges instructionCycles and its runPrefix_sound guard passes.
Security interface retains its internal pk parameter but forwards only the
actual secretKey/request arguments to organizer signingOracle.

Next signing work: SignLoopEntry, SignIndexRefine, SignExecutionSetup, SignRefine
still have old loaded input tuples and/or removed sign_publicKey references.
Do not simply erase these: prefix must derive pk. Tested standalone prototype
already does this. Consider an appended prelude reached by an entry jump to
preserve existing HASH/loop code addresses; restore the displaced ADDI x6,x0,1
before jumping back to0x1004. Prove scratch initialization/frame/stack facts
at the resumed entry. Existing loaded_scratch assumes fresh memory, so replacing
its initial state requires explicit cleared/touched scratch invariants.
Alternative is the already tested prepended prelude plus systematically updated
addresses. No implementation choice made yet; prototype is only sample-tested.

Prioritize restoration of160-level reference/security proof next, using
height commits36bf323/f0e9307 to avoid confusing numeric code offsets with tree
height. Universal cycle bound and witness charge remain uncertified.

### 2026-09-25T22:16 restore160-level security

Restored semantic height/index constants in66 Security*/Reference/Signature
modules, regenerated160-level images, and updated basic compression/signature
arithmetic. Width split is96+160=256 (three uniform-extraction calls corrected
from104+152). Instruction-proof offsets were not globally substituted.
Actual images now160levels, S=W119632, and index mask shifts32; signing still
needs its public-key derivation prelude before it satisfies the new interface.

Validated SecurityIndexMonitor2754jobs and SecuritySharedBudget2760jobs,
including their permitted-axiom guards. The lifetime collision factor is now
2^32/2^160=2^-128 and composes with the shared127-bit query budget.
Logs siggolf-contract-security160c.log, siggolf-contract-sharedbudget160.log.
This is a component security result, not a complete candidate certificate.
Signature and SignatureDecode also compile for160levels/119632bytes.
Reference-sign arithmetic121008 compressions excludes key derivation;
adding761 gives121769, below131072. Bytecode proof of this addition unfinished.

Next executable proof migration: SignIndex and VerifyIndex still describe
SLLI/SRLI x6,x6,40 and corresponding <<<40/>>>40. Change only those shift
operands to32, preserving unrelated numeric instruction offsets. Restore
SignIndexRefine/VerifyIndexRefine widths and level bounds using original height
diffs, then tackle remaining image constants (witness base0x3d3b0 vs0x3bc30,
159upperlayers vs151). Full certificate build will enumerate residuals.
Sign loaded-state pk assumptions still need actual derivation; do not fabricate
a loader pk lemma. Accepted PR12 remains unchanged; no submission this wake.

### 2026-09-25T22:21 restore functional height proofs

Migrated sign/verify index-extraction shifts40→32; exact SignIndex/VerifyIndex
build passes2723jobs (siggolf-contract-index160b.log).
Restored38 original height-change patches by individually checking then applying
`git diff f0e9307^ f0e9307 -- FILE` in reverse. Only cleanly applying candidate
files were touched; optimizer and organizer API edits outside those hunks remain.
This restores witness-copy immediates, loop bounds, checkpoint expectations,
index arithmetic, and functional memory proofs without globally changing PCs.

VerifyLoader/VerifyLoopEntry retain new layout API and now use witness base
0x3d3b0, pointer0x3d3d0, witness end370432, size119632. Generic index refinement
reads20bytes. Removed the unused loaded_index_refines signing corollary that
assumed an externally supplied pk; generic index_refines stays and verifies.
The real signing pipeline is still obligated to compute pk; no certificate
obligation was removed. loaded_randomizer_refines now uses actual3-input loader.

Remaining verifier layer bounds restored to160. Proposed execution bound in
VerifyFunctional is1730845 (10883*160-10595+145+15), excluding468witnesscycles;
1731313 would be the honest charged bound if the full proof passes. Not yet
certified. CandidateFields/Certificate/CandidateHonest still contain the old
claim1643781 and must be migrated only with the honest witness-charge proof.
Next build VerifyFunctional, fix any residual height/width constants, then
implement and prove the signer pk prelude and new loader-to-loop interface.

VerifyLoader final result: PASS2736jobs with its permitted-axiom guard,
log siggolf-contract-verifyloader160b.log. No build process remains running.

### 2026-09-25T22:27 complete verifier bound; appended signer prototype

VerifyFunctional PASS2868jobs under current contract, universally including
malformed witnesses: executionC<=1730845. New VerifyCharged.run_refines_charged
PASS2869jobs with permitted-axiom guard proves execution+witnessCycles<=1731313
(468loadingcycles). Logs siggolf-contract-verifyfunctional160.log and
siggolf-contract-verifycharged160b.log. Full four-program certificate incomplete.

Tested alternative signing prelude in ../research/contract-append-pk-probe:
entry JAL jumps to appended0x1c70; original sign words1..795 unchanged exactly.
Sets MODE1, POINTER0x20080, LEVEL159, calls encode on initiallyzero CURRENT,
then the existing enabled signing tree (whose sign_tree proof can be reused),
copies root to0x40, clears LEVEL/INDEX0..2/CURRENT0..1, restores displaced
ADDIx6,x0,1, jumps to0x1004. Sign image847words vs796. No other images altered.
Encoding is essential to satisfy sign_tree's checksum-digit assumption; the
first unencoded experiment passed sample output but was not suitable for reusing
that theorem, so the retained prototype includes encode.

All reference/rejection tests pass for retained encoded prototype:
S119632; sign121769compressions; sample verify1280367execution+468loading=
1280835cycles. Log siggolf-contract-append-pk-probe-encoded.log; measured-run.json
in prototype. These measured numbers are not substituted for universal bounds.

Next: prove appended prelude and entry suffix, then integrate. Factor
SignPrepare.initializeState_block into12-instruction suffix at0x1004; preserve
all later code addresses. Its incomingx6=1 comes from prelude. Reuse SignTree
sign_tree atlevel159/tree0 with captureenabled, pointer0x20080, selectorfalse,
encoded CURRENT0; prove secret/message/stack preservation and required cleared
scratch facts. Rebuild signer loader-to-loop proofs with computedpk and new
resource counts. Existing sign image in actual candidate still lacksprelude.
Then assemble honest witness-charge theorem, export/layout/policy/full checks.

### 2026-09-25T22:32 signer prelude proof components

New SignResume and SignDeriveRoot modules PASS2829jobs, including axiom guards;
log siggolf-contract-sign-components.log.
SignResume.initializeTail_block proves the12instructions at0x1004..0x1030 for
ANY image agreeing with those body instructions. initializeTail_equiv proves
its state equals original initialization from the virtual previous PC provided
incomingx6=1; restored_entry explicitly proves the displaced ADDI roundtrip.
No instruction at0x1000 is assumed by the suffix theorem.

SignDeriveRoot.derive_root instantiates the already-certified enabled sign_tree
at159/tree0, temporary pointer0x20080, selectorfalse, with encoded zero-message
digits. Universally returns Reference.keygen with739calls/761compressions,
instructions<=99910,cycles<=105259, restores stack and preserves every memory
word below0x20080. Requires the documented TreeContext/digit/mode/pointer
invariants; establishing those from the official initial state remains work.

Next: prove appended prelude setup/encode/root-copy/cleanup blocks and compose
with these components. The prototype remains separate; actual sign image is
still796words. Integration replaces entry instruction0x1000, so old
SignPrepare.initializeState_block and the117-instruction randomizer-entry
wrappers cannot be retained unchanged. Refactor callers to the12-instruction
suffix at0x1004 and its incomingx6=1/memory invariants, then add prelude trace.
Do not claim code-image transport from oldsign to new847-word image without
proving fetch agreement at every used instruction. Generic suffix theorem
already supplies this interface; tree code addresses remain unchanged but
its current proof is specialized to sign and must compile with the final image.
Verifier certificate component remains valid; full signing certificate pending.

### 2026-09-25 appended prelude setup

Approval-service authentication recovered. Added SignPreludeSetup: generic exact 14-instruction block from 0x1c70, establishing jump to encode at 0x1340, return address 0x1ca8, and stack preservation. Compiles with permitted-axiom guard (2737 jobs); log research/validation/siggolf-contract-prelude-setup.log. This remains conditional on explicit image fetch agreement; concrete 847-word image integration and memory/loader framing are still required. Organizer files unchanged against be68468. Next prove three memory stores preserve root/index/secret words and establish TreeContext159/0, then compose encode and tree call. No new submission.

### 2026-09-25 prelude memory and context

SignPreludeSetup now proves exact three-store memory effect, arbitrary-address frame, mode1, pointer0x20080, and TreeContext159/0 from initial index and secret-key words. Build PASS2818jobs with permitted-axiom guards for memory and context; log research/validation/siggolf-contract-prelude-memory.log. Next compose encode_subroutine and reconstruct word frames from its byte frame, then tree call at0x1ca8. Concrete image agreement and official loader composition remain outstanding; no complete candidate certificate claimed. Organizer files still identical to be68468.

### 2026-09-26 composed prelude encoder

SignPreludeEncode proves aligned low-word preservation from the encoder byte frame, including exclusion of the saved stack return address. derive_encode composes setup14 + encode454 =468 ordinary steps, returns at0x1ca8 with stack restored, zero-message digits encoded, and all aligned words below0x80600 preserved relative to setup. PASS2819jobs with permitted-axiom guards; research/validation/siggolf-contract-prelude-encode.log. Next transfer TreeContext/mode/pointer/selector through this frame and prove JAL into derive_root. Concrete image agreement and loader composition remain outstanding.

### 2026-09-26 tree entry components

SignPreludeTreeEntry proves encoder low-word frame preserves TreeContext159/0, and proves actual one-step JAL at0x1ca8 with destination0x13c8 and return0x1cac. The call preserves memory, bytes, stack and tree context. PASS2820jobs with guards, log research/validation/siggolf-contract-prelude-tree-entry.log. Concrete appended-image integration still required before composing fixed-image derive_root; these generic fetch hypotheses are not a complete certificate. Next assemble469-step entry theorem including mode/pointer/selector/digits, then resolve fixed-image integration.

### 2026-09-26 complete conditional root entry

SignPreludeEntry.derive_entry composes469 ordinary steps from0x1c70 to0x13c8, RA0x1cac, restored stack, TreeContext159/0, mode1, pointer0x20080, selector0, zero-message digits and low aligned-word preservation. PASS2821jobs with permitted-axiom guard, log research/validation/siggolf-contract-prelude-entry.log. It explicitly requires setup/encode/call fetch agreement; not yet a concrete candidate certificate. Next integrate847-word image with suffix refactoring, then root-copy/cleanup and full loader/sign certificate.

### 2026-09-26 concrete appended image entry

Added optional derive_pk generator mode and build_prelude.py generating ImagesPrelude.signPrelude (847 words), exactly matching the reference-tested prototype. Existing Images/sign remain intact while migration proceeds. SignPreludeCode proves exact setup, encoder and call fetch conditions, retained body words1..795, and instantiates prelude_entry469 steps on this concrete image. PASS2823jobs with permitted-axiom guard; research/validation/siggolf-contract-prelude-code.log. This removes entry fetch assumptions but does not transport the tree trace: next prove fetch/trace transfer for unchanged body region, or refactor fixed-image tree proofs. No submission image switched until full certificate.

### 2026-09-26 fetch agreement and trace transport

SignPreludeFetch universally proves fetch equality for every state with PC in[0x1004,0x1c70), including unaligned PCs, from retained body words. RegionTrace explicitly tracks this condition at every executed instruction and transports all resource counters and states unchanged to signPrelude. PASS2825jobs with guards; research/validation/siggolf-contract-prelude-fetch.log. Crucially derive_root still returns ordinary Trace, not RegionTrace; its regional execution evidence MUST be constructed before transport can apply. No inference of trace locality from finalPC or sample runs. Failed approach: defining Within by matching indexed Trace proof failed dependent elimination; replaced with explicit inductive RegionTrace. Next add regional composition/block constructors and instrument tree/leaf proofs, or choose generic-image proof refactoring if smaller.

### 2026-09-26 first regional tree block

Added RegionTrace.trans, one and unit-cost step constructors. SignTreeControlRegion.left_region explicitly proves all five fetch PCs for actual left-leaf control block0x13d0, retaining exact final state and5cycles. PASS2826jobs with guard; research/validation/siggolf-contract-region-control.log. Full tree regional evidence remains unfinished. Next generalize this block to right call0x13e4 and instrument enter/return, leaf loops and hashing; final return state may leave region and must stay unrestricted.

### 2026-09-26 regional stack and right-call proofs

Added right tree-control block regional proof, generic enter/return regional traces, and all five concrete signer stack sites (tree/leaf enter; leaf/bottom/node return). Return fetches stay in body while final return destination is unrestricted. PASS2828jobs with guards, research/validation/siggolf-contract-region-stack.log. Remaining work is regional leaf/hash/chain and tree composition, not stack sites. Existing full tree Trace cannot yet be transported.

### 2026-09-26 direct appended-image chain proofs

A smaller integration route works: re-elaborate signer execution proofs in Signing.Prelude using generic bytecode components and concrete signPrelude code facts. PreludeChainStep proves actual96-instruction103-cycle core; PreludeChainLoop, PreludeChainUnselected and PreludeChainCapture prove universal remaining-chain execution/endpoints including captured signature values directly on signPrelude. PASS2787jobs with permitted-axiom guards; research/validation/siggolf-contract-prelude-chains.log. This avoids requiring regional instrumentation for these components. Existing regional framework remains valid but is not needed for directly reproved chains. Next port upper-leaf loop/entry/calls using these concrete chain proofs and generic secret/endpoint/compression code, then upper tree and derive_root. Existing signer certificate remains incomplete.

### 2026-09-26 complete direct upper-leaf calls

Direct concrete-image port now covers secret preparation, STEP reset, selected/unselected iterations and46-chain loops, leaf compression/return, entry, and complete selected/unselected upper-leaf calls. Parent state/data types preserved; new execution theorems live in Signing.Prelude. Both full calls prove exact369calls/380compressions and bounds49895instructions/52566cycles on signPrelude. PASS2824jobs with top-level permitted-axiom guards; research/validation/siggolf-contract-prelude-leaf.log. Next port TreeSettings upper-call adapter, TreeLeaves and TreeFinish on signPrelude, then specialize level159/tree0 to derive public key. Bottom leaf not needed for initial pk derivation but needed later for full signer. No complete signer certificate yet.

### 2026-09-26 concrete public-key derivation

Direct image proofs now cover upper-tree settings/calls, both leaves, sibling serialization, node hash and return. PreludeDerivation.derive_public_key composes concrete469-step entry and root derivation:739calls761compressions, instructions≤100379, cycles≤105728, actual return0x1cac, restored stack, reference public key in CURRENT and aligned low-word frame. PASS2851jobs with permitted-axiom guard; research/validation/siggolf-contract-prelude-derivation.log. Assumptions are explicit initial secret/index/zero-buffer state at0x1c70; actual loader jump and final root-copy/cleanup/resume still need composition. Next prove appended root copy0x1cac→public-key0x40 and cleanup/resume, then loader-to-prelude entry and full signing suffix.

### 2026-09-26 root copy and cleanup

PreludeRootCopy.root_copy proves16 actual ordinary steps0x1cac→0x1cd4, writing CURRENT words to pk0x40/0x48 and preserving other memory and stack. PreludeCleanup proves26steps resetting LEVEL, three INDEX words, two CURRENT words, x6=1, then actual JAL to0x1004. Exact cleanup memory effect and stack preservation are proved. PASS2853jobs with block/copy guards; research/validation/siggolf-contract-prelude-cleanup.log. Next compose derivation+copy+cleanup (extra42cycles), then actual loader entry jump and full signing suffix.

### 2026-09-26 prepared signer state

PreludePrepared.prepare_signer composes derivation/copy/cleanup: actual returnPC0x1004,x6=1,stack0x1000000,correct pk words,zero LEVEL/INDEX/CURRENT, low aligned-input frame excluding pk. Bound≤100421instructions/105770cycles,739calls761compressions. PreludeJump proves actual0x1000→0x1c70 jump and memory/stack frame. PASS2855jobs with guards; research/validation/siggolf-contract-prelude-jump.log (includes prepared theorem). Next establish actual initialState loader facts for signPrelude and compose jump with prepared theorem; then full suffix certification.

### 2026-09-26 official signer loader

PreludeLoader defines a research submission selecting signPrelude and proves image validity, actual official-loader scratch words zero above0x80000, stack0x1000000,entryPC0x1000 and four secret-key words via official byte loading. No public-key input assumed. PASS2856jobs with guards; research/validation/siggolf-contract-prelude-loader.log. Next use these facts to discharge every prepare_signer assumption after entryJump and compose total bound≤100422instructions/105771cycles. Full suffix remains unfinished.
