# Polynomial-coded OTS: implications for the competition

Source: the organizer-supplied September 9 messages and image of annex A,
“Polynomial coding”. Only that displayed page is reviewed here; the complete
signing/decoding algorithm and security proof were not provided. The prior
six-page note and [Top of the Hypercube](https://eprint.iacr.org/2025/889) are
context, not interchangeable security results for this new construction.

## What the displayed construction does

It uses 64 independent 136-bit seeds. A 512-bit hash output supplies 64 byte-sized
coefficients per column of a degree-at-most-63 polynomial over GF(256). Evaluating
at all 256 field elements gives a 256-by-64 byte table. Each 64-byte row is hashed
to a 128-bit digest; a four-ary Merkle tree of height four authenticates the 256
row digests. The public key is the root. Its abstract keygen count is
`64 + 256 + (64 + 16 + 4 + 1) = 405` calls.

The illustration reveals eight seeds, supplies the other 56 entries for each
opened row, and describes 56 tree-proof digests. It does not specify the complete
row-selection codebook or verifier, so no full signing/verification score or
strong-unforgeability claim is derived from it here.

## The cost-model warning is real

The organizer's subsequent clarification is a constrained-search statement: with
signature size and signing budget fixed, minimizing verification can favor a
Reed–Solomon-coded construction rather than a hash chain. We retain that search
direction, without interpreting the displayed page as a proof of global
optimality or a complete competition entry.

The annex allows a 64-byte output per call and free field arithmetic. Our oracle
returns 32 bytes and now charges `ceil(inputBytes / 64)` per call (v0.15), including
all supplied domain-separation bytes. Under the **assumed**
16-byte address layout used by the current OTS experiments:

| Keygen operation | Assumed implementation | Weighted units |
| --- | --- | ---: |
| 64 coefficient expansions | two calls per 17-byte seed; 33-byte tagged input | 128 |
| 256 row hashes | 80-byte tagged inputs | 512 |
| 85 Merkle parents | 80-byte tagged inputs | 170 |
| Total | same displayed shape, not re-optimized | 810 |

This is a source-level re-metering, not a Lean cost certificate or a practical
hash instantiation. A concrete layout, domain-separation/simulation proof and
re-optimization may change it. It is not comparable to a full SPHINCS score.
The earlier 1,279-unit estimate used the superseded 32-byte input unit; 810 is
a meter revision, not an algorithmic speedup. The 64-byte input unit does not
restore the annex's 64-byte output. The literal ceiling charges an empty input
zero hash-work units, but raw security queries and execution work remain charged.

Naive Horner evaluation of all columns at all points uses
`64 * 256 * 63 = 1,032,192` GF(256) multiplications and the same number of additions.
Faster multipoint evaluation or other algorithms may reduce that. These counts
are **not** RISC-V cycles; neither field operations nor codebook unranking may be
omitted from the execution profile. The raw table alone occupies 16,384 bytes,
before seeds, coefficients, tree nodes, decoder tables and scratch memory.

Reproduce these limited arithmetic checks:

```sh
python3 scripts/polynomial_annex.py
python3 -m unittest discover -s tests -v
```

## Security and template implications

- Public polynomial/field arithmetic adds no hardness assumption by itself.
  Do not reject a construction merely for using Reed–Solomon coding; require its
  actual ROM security proof and full-program resource accounting.
- The 256 evaluations are correlated. Any 64 distinct evaluations determine a
  degree-at-most-63 column polynomial. This is a boundary the leakage proof must
  handle, not a demonstrated attack on this OTS. Multiple exposures/composition
  cannot be justified by counting hash-graph cuts alone.
- Hash-derived coefficients are not 64 independently sampled secret bytes in
  the implemented key: the seed/oracle relation must stay in the security game.
- The existing optional graph DSL has 128-bit vertices and direct hash gates.
  It does not yet represent 8-bit coded entries, 136-bit seeds, or deterministic
  field-operation nodes. Do not shoehorn the annex into it and inherit its
  incomparability/counting assumptions. An extended typed circuit model needs
  correctness, leakage and instruction-cost proofs; direct pure-ROM scheme
  submissions must remain an alternative to templates.

## Current reviewed decisions (2026-09-11)

Both stages use `c * signatureBytes + verificationWork` within matched games
and profiles. The organizer-owned rational price c is pending calibration; no
scalar ranking is issued until then. The Pareto frontier remains useful meanwhile.
Stage 1 is broader than OTS and does not assume components are used fully black-box.

Hard account budgets remain 1.5 s signing, 60 s keygen and 64 KiB working RAM.
Full-program worst-case certificates must include arithmetic, retries and storage;
the hash count alone cannot establish them. Expected work is optional reporting,
not a replacement for a hard cap. Signing-failure probability is separate.

The September 13 R9 clarification makes these worst-case limits mandatory for
eligibility, including every failure/retry path and all required precomputation.
Separate raw-query caps include empty and repeated calls: weighted hash counts
alone must not allow honest query padding to make the security slope vacuous.
The complete executable and resource certificates remain to implement.

The security claim is pure ROM, public keys <= 32 bytes, total query work
Q = qH + qS (including challenger hashes), with exact constants and same-scheme
124-bit / 100-bit floors at 2^20 / 2^32 requests. No constants-dropping rule or
mandatory public cache/presign interface remains. The annex does not yet supply
these certificates, and its arithmetic estimates are not a new baseline.

## Historical decisions applied on 2026-09-10

The following records the superseded scoring decisions, not the current objective.

Update, spec v0.16 (later the same day): both stages now minimize
`size * verification`, with signing and keygen work fixed as hard budgets (1.5 s
signing, 1 minute keygen). The four-factor formula below is retained as a research
view only.

Both stages used `size * signing * verification * keygen^(1/4)` in v0.14/v0.15. This formula may
be instantiated with separately identified hash-work and execution-cost profiles.
Do not mix units or expected/worst-case signing semantics on one board. Preserve
the full frontier; do not proclaim the hash-minimal shape a practical winner.

Hard keygen/signing latency, verification execution and memory gates remain
required for promotion. The wallet budgets are 1 minute keygen / 1.5-second signing as of v0.16. Their implementation
and the cycle profile remain launch work. At that time the final profile and signing-work semantics were still open;
the current objective no longer scores signing. Worst-case failure probability
remains a separate proof obligation.

At that revision the cryptographic interface and audited upstream pin were unchanged. The v0.15
protected hash-work meter was updated by organizer decision, independently of
any candidate's security proof; the legacy claim still lacks K/S certificates.
The next execution work is a
metered encoding kernel plus exact oracle/program binding, not an aesthetic ban
on unusual constructions or a silent switch to a different hash oracle.
