# Binary hypertree candidate

This is an experimental four-program candidate, not a certified submission. `keygen`, `sign`, `expand`, and `verify` have concrete RISC-V images in `SigGolfCandidate/Hypertree/Images.lean`.

The signer derives a 32-byte randomizer as H(domain 6, seed, message) and includes it in the signature. The index is the low 160 bits of H(domain 5, public key, message, randomizer). The randomizer addresses the deterministic encoding’s birthday attack; its security reduction remains unfinished. The construction uses this index, two hash-preimage leaves at the bottom, and 159 layers of two-leaf Merkle trees with base-8 Winternitz signatures (46 chains, 128-bit values). It has no FORS component. Signing ignores the public cache. Expansion copies the signature.

Signature and witness size: 119,632 bytes each. The reference algorithm uses 761 key-generation compressions and 121,008 signing compressions. One test run matches these counts in the bytecode interpreter; this is not a universal resource proof.

Regenerate images with `python3 examples/hypertree/build.py`. Compare bytecode with the independent algorithm using `python3 examples/hypertree/check.py`. This uses SHA-256 as a concrete test oracle; `measured-run.json` records that run, not a worst-case certificate.

`lake build SigGolfCandidate` checks:

- Static admission of all four exact images.
- Functional correctness of the reference hypertree for every seed, message, and fixed oracle.
- The Winternitz checksum property: changing the signed digest requires moving backward in at least one chain.
- Reference compression-count arithmetic.
- Image-independent protected copy-loop and HASH execution lemmas, including exact copied contents and preservation outside the destination.
- Key-generation entry and exit blocks, the signing comparison block, and the randomizer HASH/output-copy block.
- An abstract adaptive search bound and security-constant arithmetic; connecting these to the actual random-oracle experiment remains required.
- The actual expansion bytecode: every input succeeds in exactly 89,733 cycles with zero hash calls, and every source-buffer byte is copied to the output buffer. These proofs use the organizer’s loader, interpreter, and output decoder.

Still required: input-serialization round trips, bytecode refinement and universal resource bounds for key generation, signing, and verification; the honest-execution success and exponential compression-budget statements; and security in the competition game. No `SigGolf.Certificate` is claimed.
