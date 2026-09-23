# Binary hypertree candidate

The four RISC-V images have a complete Lean certificate: `SigGolfCandidate.Hypertree.Candidate.certificate : SigGolf.Certificate submission 3316075`, in [Certificate.lean](../../SigGolfCandidate/Hypertree/Certificate.lean).

| Parameter | Value |
| --- | ---: |
| Signature bytes S | 119,632 |
| Witness bytes W | 119,632 |
| Maximum honest verification cycles C | 3,316,075 |
| Score S × C | 396,708,684,400 |

The signer derives a 32-byte randomizer as H(domain 6, secret key, message) and includes it in the signature. The index is the low 160 bits of H(domain 5, public key, message, randomizer). The construction uses two hash-preimage leaves at the bottom and 159 layers of two-leaf Merkle trees with base-8 Winternitz signatures (46 chains, 128-bit values). It has no FORS component. Signing ignores the public cache. Expansion copies the signature.

The certificate establishes all organizer requirements for the exact images in [Images.lean](../../SigGolfCandidate/Hypertree/Images.lean):

- Static admission, including fixed sizes and image limits.
- Termination below 2^32 cycles for every typed input and every oracle, including adversarial caches, signatures, and witnesses.
- Honest success for every secret key, message, and oracle, implying the required simultaneous all-message success probability.
- Exponential compression budgets for an independent uniform message and random oracle.
- Security at every total hash-call budget Q: forgery probability at most Q / 2^127, against adaptive adversaries with up to 2^24 signing requests. Both final-submission forms and all honest and adversarial hash calls are included.
- The claimed verification cycle bound.

The proof connects the organizer's bytecode security experiment to the reference scheme, then bounds secret key guesses, graph contacts, nonce guesses, and index collisions in one shared simulation. The final certificate's axiom guard permits only `propext`, `Classical.choice`, and `Quot.sound`.

| Program | Proved cycle bound | Hash calls | Compressions |
| --- | ---: | ---: | ---: |
| Key generation | 82,446 | 739 | 761 |
| Signing | 16,922,843 | 117,508 | 121,008 |
| Expansion | 89,733 | 0 | 0 |
| Verification | 3,316,075 | ≤ 51,841 | ≤ 53,602 |

Key-generation and expansion counts are exact. Signing hash counts are exact for a matching public key; its cycle count is an upper bound. Verification bounds cover arbitrary typed witnesses.

Check the rules, regressions, and complete certificate with `lake build SigGolf SigGolfTests SigGolfCandidate`.

Regenerate images with `python3 examples/hypertree/build.py` and key-generation resource checkpoints with `python3 examples/hypertree/keygen_resources.py`. Run the independent algorithm/bytecode comparison with `python3 examples/hypertree/check.py`. Its SHA-256 sample is recorded in `measured-run.json`; the universal bounds and random-oracle security come from the Lean proofs.

The verifier cycle proof uses the Winternitz checksum to bound the sum of chain lengths. The 46 digits sum to at least 14, so at most 308 chain hashes are needed per upper leaf. This tightens the certified cost without changing the program images or signature format.

The bottom layer is bounded separately: 116 cycles for its leaf, 236 for its tree, and 288 for the full layer including dispatch. The complete bound is `145 + 288 + 159 * 20853 + 15 = 3316075` cycles.

The verifier unrolls the two 16-byte copies inside each chain hash. Each replacement preserves all registers, memory, and the following program counter while saving seven cycles. Together with the shared-base header, the complete chain iteration costs 56 cycles instead of 103. `FastCopy16.lean` proves the replacement and connects it to the actual verifier image.

The shared-base header uses 24 instructions instead of 42. `FastChainHeader.lean` proves exact final-state equivalence and execution; `FastHeaderChain.lean` connects its 58-cycle core to the complete verifier. All following instruction addresses remain unchanged.

`AddressReuseProof.lean` proves the 27-instruction full header setup and two 9-instruction copies preserve the original complete machine states. `AddressReuseChain.lean` connects these replacements to the actual image, proving a 53-cycle chain core.

`FastIncrement.lean` proves a six-instruction counter update is exactly equivalent to the former eight-instruction fragment, including the backward jump. Two skipped padding words retain the original instruction layout.

`Copy6.lean` proves six-step copies preserve the memory, stack, return-address, and program-counter guarantees required by the verifier. `Copy6Chain.lean` connects them to the actual image, establishing a 40-step/47-cycle chain core. Unused temporary registers may change.

`FusedPrepare.lean` combines the input copy and HASH header setup into 31 steps, reaching exactly the previous prepared state. `FusedChain.lean` establishes the resulting 38-step/45-cycle core.
