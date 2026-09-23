# Hypertree optimization log

Research starts from organizer beta commit `7c2d18e4b797e81b312680e18ae119233d325729` and the published first-record candidate. All experiments below preserve the four exact RISC-V images, the reference scheme, the signature format, and the organizer definitions.

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
