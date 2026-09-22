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
- Universal key-generation success, strict termination, and exact resource counts for the submitted bytecode.
- The complete signer randomizer/index prefix through the official loader: 226 instructions, 256 cycles, two hash calls, four compressions, and the exact reference index.
- Canonical signature serialization, with fixed size and mutually inverse encoding/decoding; every signature byte is accounted for.
- Concrete random-oracle query and cache-replacement lemmas, seed-guessing bounds, monadic reference key generation/signing/verification, and security-constant arithmetic. The complete security reduction remains unfinished.
- The actual expansion bytecode: every input succeeds in exactly 89,733 cycles with zero hash calls, and its returned typed value equals the original signature. These proofs use the organizer’s loader, interpreter, and output decoder.

Still required: full functional bytecode refinement for key generation, signing, and verification; universal signing/verification resource bounds; the honest-execution success and exponential compression-budget statements; and security in the competition game. No `SigGolf.Certificate` is claimed.
