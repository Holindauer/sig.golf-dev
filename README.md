# sig.golf · beta rules

Goal: design a **stateless hash-based signature scheme**,  minimizing *signature size* x *maximum verification cycles in RISC-V*.

## Submission

1. The five RiscV programs below.
2. Claimed signature sizes `S`, witness size `W`, and an upper bound `C` on the number of RiscV cycles at verificiation.
3. Lean 4 proofs.

score = S * C

## Parameters

| Constant        |                 Value |
| --------------- | --------------------: |
| `BUDGET_KEYGEN` |     2^20 compressions |
| `BUDGET_GRIND`  |     2^20 compressions |
| `BUDGET_SIGN`   |     2^17 compressions |
| `BUDGET_EXPAND` |     2^20 compressions |
| `FAILURE`       |                2^-256 |
| `LIFETIME`      | 2^24 signing requests |
| `SECURITY_BITS` |                   127 |
| `CYCLE_LIMIT`   |           2^40 cycles |

Every object has a fixed size:

| Object            |                Bytes |
| ----------------- | -------------------: |
| Message digest    |                   32 |
| Seed              |                   16 |
| Public key        |                   16 |
| Cache             |       2^17 (128 KiB) |
| Nonce             |                   16 |
| Compact signature |              `S` ≥ 1 |
| Expanded witness  | `W` ≤ 2^17 (128 KiB) |

## Programs

| Program  | Inputs                                  | Outputs                          | Context     |
| -------- | --------------------------------------- | -------------------------------- | ----------- |
| `keygen` | Seed                                    | Public key and cache, or failure | Enclave     |
| `grind`  | Message, public key                     | Nonce or failure                 | Signer host |
| `sign`   | Seed, public key, cache, message, nonce | Signature or failure             | Enclave     |
| `expand` | Message, public key, signature          | Witness or failure               | Prover host |
| `verify` | Message, public key, witness            | Accept or reject                 | zkVM        |

The seed is secret. The cache is public and untrusted. Intuitively, the witness contains the 'information' of the signature, but in a potentially "decompressed" way, easier to verify (Example: unpruning Merkle paths). The trivial `expand` algorithm simply sets the witness to the signature.

## Model and costs

All programs and the adversary share a random oracle H from finite bit strings to 32-byte outputs (modelling a hash function).

The security statement in Lean counts the number of calls to H, independently of the size of the input.
For practical reasons, the budgets, as well as the performance of the RiscV verifier count how many *compressions* are required to compute each hash. Hashing n bits costs `max(1, ceil(n / 512))` compressions.

| Operation                                        | Cost                                                   |
| ------------------------------------------------ | ------------------------------------------------------ |
| Ordinary instruction, including loads and stores | 1 cycle                                                |
| HASH                                             | 8 cycles per compression (no extra instruction charge) |
| HALT                                             | 1 cycle                                                |


## Required Lean statements

### Honest execution

For any `seed`, `message` and oracle H, consider the following experiment:

1. `keygen(seed)` returns the `public key` and `cache`.
2. `grind(message, public key)` returns the `nonce`.
3. `sign(seed, public key, cache, message, nonce)` returns the `signature`.
4. `expand(message, public key, signature)` returns the `witness`.
5. `verify(message, public key, witness)` returns the verdict.

Stop at the first failure. We say the `experiment succeeds` when all stages succeed and verification accepts.

`K_P` counts program P's compressions in this experiment, including retries and failed attempts; it is zero if P is never reached. For each fixed seed and H, `Kmax_P` is the maximum of `K_P` over all messages. `BUDGET_P` denotes P's named budget.

1. **Termination:** experiment terminates for every seed, message, and oracle.
2. **Success:** for every seed, `Pr_H[experiment succeeds for every message] >= 1 - FAILURE`.
3. **Compression budgets:** for every seed, `E_H[2^(Kmax_P / BUDGET_P)] <= 2` for each P in {`keygen`, `grind`, `sign`, `expand`}.
4. For every seed, message and oracle, if the experiment succeeds, verify runs no more than `C` RiscV cycles.

(`Pr_H`means probability over `H`, `E_H` means expectation over `H`.)

### Security

Consider the following experiment for a classical, probabilistic, ubounded, adversary `A` and hash-call budget Q >= 1:

- Sample H and a uniform `seed` independently, unfirmly.
- Initialize a hash-call counter and an empty transcript T.
- Run `keygen(seed)` and give A the result (`public key` and `cache`); failure ends the experiment without a win.
- `A` may adaptively query two oracles:
  - **`random_oracle(input_A)`:** return H(input_A)
  - **`signing_oracle(message_A, nonce_A, cache_A)`:** run `sign` with these inputs and the original `seed` and `public key`. Return the signature or failure. Record each returned `(message_A, signature)` in T. Allow at most `LIFETIME` requests. `cache_A` may differ from the original `cache`.
- `A` makes one final submission, choosing one of the following two forms:
  1) `A` submits (`message_A`, `witness_A`). `A` wins if:
     - Running `verify` with these inputs and the original `public key` accepts.
     - For every message `(message, signature)` in T, `message` != `message_A`. (weak unforgeability)
     - The total number of hash call to H, including key generation, signing, `A`'s queries, and verification, is at most `Q`.
  2) `A` submits (`message_A`, `signature_A`). `A` wins if:
     - `expand(message_A, public key, signature_A)` succeeds with a witness, and `verify(message_A, public key, witness)` accepts.
     - For every message `(message, signature)` in T, `(message, signature)` != `(message_A, signature_A)`. (strong unforgeability)
     - The total number of hash calls to H, including key generation, signing, `A`'s queries, expansion, and verification, is at most `Q`.

1. **Security:** for every advserary `A` and query budget Q, `Pr[A wins] <= Q / 2^SECURITY_BITS`, with probability over the seed, H, and `A`'s randomness.

### Program requirements

1. **Sizes:** successful outputs have their declared fixed sizes.
2. **Memory:** each program uses at most 1 MiB of memory.
3. **Correctness:** whenever `sign` returns a signature and `expand` returns a witness from it, `verify` accepts, using the same message, public key, and H.
4. **Statelessness:** signing reuses the seed and honest cache without updates, counters, consumed one-time keys, or other persistent state.
5. **Termination:** every program terminates with a result or failure in fewer than `CYCLE_LIMIT` cycles, for every input and oracle.


## RISC-V interface

Use [RV64I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html) and the [M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).

Each program satisfies **`4 × instruction count + embedded-data bytes < 2^20`**, checked directly at submission.

### Code and memory

Code occupies a separate, immutable instruction address space. Instruction i is at `0x1000 + 4 × i`.

Memory occupies `0x000000`–`0x0FFFFF` (1 MiB), including embedded data, inputs, outputs, scratch space, and stack.

Initialize memory to zero. Load D embedded bytes at `data_base = 16 × floor((0x100000 - D) / 16)`. Initially, `sp = data_base` and `PC = 0x1000`; all other integer registers are zero.

### Inputs and outputs

Inputs and outputs use the same addresses, fixed for each submission:

| Address                     | Buffer     |
| --------------------------- | ---------- |
| `0x00`                      | Message    |
| `0x20`                      | Seed       |
| `0x40`                      | Public key |
| `0x50`                      | Nonce      |
| `0x60`                      | Cache      |
| `0x20060`                   | Signature  |
| `0x20060 + 8 × ceil(S / 8)` | Witness    |

Load the inputs and read the outputs listed in the Programs table at their declared sizes. Unused input fields stay zero.

HALT ends execution with `a0 = 1` for success, or `a0 = 0` for failure. For `verify`, these mean acceptance and rejection, respectively.

### System calls

ECALL selects one of two services through `t0`:

| `t0` | Service | Arguments                                                                |
| ---: | ------- | ------------------------------------------------------------------------ |
|    0 | HALT    | Status and outputs above                                                 |
|    1 | HASH    | `a0 = input address`, `a1 = input length in bits`, `a2 = output address` |

HASH writes H's 32-byte answer at the output address.

### Further Details

- **Instructions:** encodings are 32 bits. Fetching outside the code or at a non-4-byte-aligned address fails. `FENCE` has no effect; `EBREAK` fails.
- **Registers:** `x0`–`x31` are 64 bits. `x0` always reads zero and ignores writes. Aliases are `sp = x2`, `t0 = x5`, and `a0`–`a2 = x10`–`x12`. PC is separate.
- **Memory access:** addresses count bytes; multi-byte integers are little-endian. Loads and stores access only memory, not code. Accesses of 1, 2, 4, or 8 bytes require alignment to their size. Misaligned accesses fail.
- **Bounds:** every memory access and buffer must fit completely in memory. For unsigned byte address p and length n, require `p + n <= 0x100000`. All size, layout, and bounds calculations use mathematical integers without overflow. Instruction arithmetic and effective-address calculation follow RV64IM.
- **Buffer layout:** cache, signature, and witness occupy separate consecutive areas, with up to seven alignment bytes after the signature. Require `0x20060 + 8 × ceil(S / 8) + W <= data_base` for each program.
- **Input loading:** reject incorrect sizes or buffers extending beyond `data_base`. Starting addresses are 8-byte aligned; lengths need not be multiples of eight.
- **Output extraction:** read each output at its declared size from its fixed address in final memory. On failure, ignore output buffers.
- **HASH arguments:** addresses and bit length n are unsigned 64-bit values. The input’s `ceil(n / 8)` bytes and the output’s 32 bytes must fit entirely in memory; check this before any oracle call or write. Both input and output addresses must be 8-byte aligned.
- **HASH execution:** read exactly n bits in increasing byte-address order, least-significant bit first within each byte; ignore unused high bits of the final byte. Read all input before writing the answer, so buffers may overlap. Preserve integer registers and advance PC by 4.
- **Faults:** unknown services, invalid arguments, invalid HALT statuses, invalid instruction encodings, and memory or instruction-fetch faults end the program with failure (`verify` rejects).
