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
