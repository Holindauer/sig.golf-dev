# Third-party source notices

`verifier/check-submission-imports.sh` is adapted from proximity-prize/proximity-prize at `da60d54326afbe85d18a94d0e5c479a724e55ad7` (Apache-2.0). Changes replace the challenge names, admitted metric files and library prefixes, and forbid native_decide. `verifier/comparator-leanchecker.patch` is the compatibility patch from that harness, with expanded diff context. See `LICENSE`.

The downloaded comparator and lean4export retain their own source headers and licenses in `verifier/.tools/`. VCVio, Mathlib and the other locked dependencies retain their licenses in their Lake packages. Game design follows the public leanVM-b XMSS/SPHINCS statements cited in docs/IMPLEMENTATION.md; no upstream scheme proof is bundled as an accepted submission.
