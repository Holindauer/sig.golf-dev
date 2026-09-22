# Binary hypertree candidate

This is an experimental four-program candidate, not a certified submission. `keygen`, `sign`, `expand`, and `verify` have concrete RISC-V images in `SigGolfCandidate/Hypertree/Images.lean`.

The construction uses a 160-bit message-derived index, two hash-preimage leaves at the bottom, and 159 layers of two-leaf Merkle trees with base-8 Winternitz signatures (46 chains, 128-bit values). It has no FORS component. Signing ignores the public cache. Expansion copies the signature.

Signature and witness size: 119,600 bytes each. The reference algorithm uses 761 key-generation compressions and 121,006 signing compressions. One test run matches these counts in the bytecode interpreter; this is not a universal resource proof.

Regenerate images with `python3 examples/hypertree/build.py`. Compare bytecode with the independent algorithm using `python3 examples/hypertree/check.py`. This uses SHA-256 as a concrete test oracle; `measured-run.json` records that run, not a worst-case certificate.

`lake build SigGolfCandidate` checks static image admission, a generic Winternitz chain-recovery lemma, and reference-count arithmetic. Still required: bytecode refinement, universal termination and cycle bounds, completeness, compression bounds for the actual programs, and security in the competition game. No `SigGolf.Certificate` is claimed.
