# Binary hypertree candidate

This is an experimental four-program candidate, not a certified submission. `keygen`, `sign`, `expand`, and `verify` have concrete RISC-V images in `SigGolfCandidate/Hypertree/Images.lean`.

The signer derives a 32-byte randomizer as H(domain 6, seed, message) and includes it in the signature. The index is the low 160 bits of H(domain 5, public key, message, randomizer). The randomizer addresses the deterministic encoding’s birthday attack; its security reduction remains unfinished. The construction uses this index, two hash-preimage leaves at the bottom, and 159 layers of two-leaf Merkle trees with base-8 Winternitz signatures (46 chains, 128-bit values). It has no FORS component. Signing ignores the public cache. Expansion copies the signature.

Signature and witness size: 119,632 bytes each. Key generation is proved to succeed for every seed and fixed oracle in 81,342 cycles, with 739 hash calls and 761 compressions. The reference signing algorithm uses 121,008 compressions; the matching interpreter test is not yet a universal signing resource proof.

Regenerate images with `python3 examples/hypertree/build.py` and the kernel-checked key-generation resource checkpoints with `python3 examples/hypertree/keygen_resources.py`. Compare bytecode with the independent algorithm using `python3 examples/hypertree/check.py`. This uses SHA-256 as a concrete test oracle; `measured-run.json` records that run, not a worst-case certificate.

`lake build SigGolfCandidate` checks:

- Static admission of all four exact images.
- Functional correctness of the reference hypertree for every seed, message, and fixed oracle.
- The Winternitz checksum property: changing the signed digest requires moving backward in at least one chain.
- Reference compression-count arithmetic.
- Image-independent protected copy-loop and HASH execution lemmas, including exact copied contents and preservation outside the destination.
- End-to-end key-generation refinement through the official loader and output decoder, including the exact public key, zero public cache, universal success, strict termination, and exact resource counts.
- End-to-end signer refinement through the official loader and output decoder: the exact canonical signature for a matching public key, arbitrary public cache, at most 16,800,271 cycles, exactly 117,508 hash calls, and 121,008 compressions.
- The complete Winternitz encoding subroutine shared by signing and verification: all 46 digits, 454 ordinary instructions, and stack restoration.
- End-to-end verifier refinement for arbitrary typed inputs: all 160 layers, exact acceptance equivalence with the decoded reference signature, and at most 5,883,520 cycles.
- The complete shared parent-node computation and return, matched to the reference construction and checked against the verifier’s code.
- Complete key-generation and verifier chain loops matched to the reference walk, signer endpoint recovery with exact hash counts, and the signer’s conditional signature/sibling writes. The verifier’s witness loads and digit initialization connect directly to its chain loop.
- Exact secret derivation and leaf-compression HASH query serialization, with shared endpoint-store controls.
- Complete key-generation tree execution, signer upper-tree execution with exact signature capture, and verifier tree execution for both bottom and upper layers. Every verifier tree call handles arbitrary witness contents in at most 36,264 cycles, with stack restoration and input preservation.
- Canonical signature serialization, with fixed size and mutually inverse encoding/decoding; every signature byte is accounted for.
- Concrete random-oracle query and cache-replacement lemmas, seed-guessing bounds, exact private/public oracle simulations of reference key generation and signing, a seed-erasure game hop, monadic verification, hash-call cutoff accounting, randomized-index bounds, full-path forgery extraction, a concrete reference security experiment, independent uniform labels for the complete addressed hash graph, equivalence between hidden graph precomputation and the observable lazy random oracle, and exact signing-output dependence on revealed graph points. The causal contact-probability bound and complete security reduction remain unfinished.
- The actual expansion bytecode: every input succeeds in exactly 89,733 cycles with zero hash calls, and its returned typed value equals the original signature. These proofs use the organizer’s loader, interpreter, and output decoder.

The actual organizer statements for admission, universal termination, completeness, exponential compression budgets, and verification cycles are proved. Security remains open, including the adaptive contact bound and charged-budget simulation. `certificate_of_secure` explicitly requires that missing security theorem; no complete `SigGolf.Certificate` is claimed.
