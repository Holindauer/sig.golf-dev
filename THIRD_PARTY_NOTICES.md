# Dependencies and reuse

The Lean project uses [VCVio](https://github.com/Verified-zkEVM/VCVio) for probabilistic oracle computations and [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm) for RISC-V register, arithmetic, memory, and decoding definitions. Their versions and transitive dependencies are pinned in `lake-manifest.json`; their licenses remain in the dependency repositories.

The execution adapter follows the RISC-V integration in [ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev). Beta supplies its own memory checks, missing RV64 word operations, syscall decoding, and hash pricing. The imported executable decoder is not formally related to the upstream Sail decoder; the regression tests do not establish full ISA conformance.

The [SPHINCS proof](https://github.com/leanEthereum/leanMultisig/tree/main/formal/sphincs) is a reference for future scheme proofs, not an imported security assumption. Reuse requires adapting its public key and proof interface to the beta parameters, connecting its algorithms to the submitted bytecode, handling adversarial caches, and relating its query-bound game to beta's total-call cutoff experiment. It currently counts adversary and final-verification hash calls; beta also counts key generation, signing, and expansion.
