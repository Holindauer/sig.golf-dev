# sig.golf · beta rules

Design a **stateless hash-based signature scheme** minimizing `S × C`: signature bytes times maximum honest verification cycles.

## Submission

1. The four RISC-V program images below, including embedded data.
2. Nonnegative integers `S`, `W`, and `C`: signature bytes, witness bytes, and verification cycles.
3. Lean 4 proofs of the statements below for those exact images, sizes, and bound.

## Parameters

| Constant        |                 Value |
| --------------- | --------------------: |
| `BUDGET_KEYGEN` |     2^20 compressions |
| `BUDGET_SIGN`   |     2^17 compressions |
| `BUDGET_EXPAND` |     2^20 compressions |
| `FAILURE`       |                2^-256 |
| `LIFETIME`      | 2^24 signing requests |
| `SECURITY_BITS` |                   127 |
| `CYCLE_LIMIT`   |           2^32 cycles |

Every object has a fixed size in bytes:

| Object            |                Bytes |
| ----------------- | -------------------: |
| Message digest    |                   32 |
| Seed              |                   16 |
| Public key        |                   16 |
| Cache             |       2^17 (128 KiB) |
| Compact signature |              `S` ≥ 1 |
| Expanded witness  | `W` ≤ 2^17 (128 KiB) |

## Programs

| Program  | Inputs                           | Outputs                          | Context     |
| -------- | -------------------------------- | -------------------------------- | ----------- |
| `keygen` | Seed                             | Public key and cache, or failure | Enclave     |
| `sign`   | Seed, public key, cache, message | Signature or failure             | Enclave     |
| `expand` | Message, public key, signature   | Witness or failure               | Prover host |
| `verify` | Message, public key, witness     | Accept or reject                 | zkVM        |

The seed is secret. The cache is public and untrusted. `expand` converts the compact signature into a verification witness, for example by restoring pruned Merkle paths. It may simply copy the signature when `S = W`.

## Model and costs

All programs and the adversary share a random oracle H.

Security counts calls to H. Program budgets and HASH cycles count compressions: hashing n bits costs `max(1, ceil(n / 512))` compressions.

RiscV cycle breakdown:

| Operation                                        | Cost                                                   |
| ------------------------------------------------ | ------------------------------------------------------ |
| Ordinary instruction, including loads and stores | 1 cycle                                                |
| HASH                                             | 8 cycles per compression (no extra instruction charge) |
| HALT                                             | 1 cycle                                                |

## Required Lean statements

### Honest execution

For any `seed`, `message` and oracle H, consider the following experiment:

1. `keygen(seed)` returns the `public key` and `cache`.
2. `sign(seed, public key, cache, message)` returns the `signature`.
3. `expand(message, public key, signature)` returns the `witness`.
4. `verify(message, public key, witness)` returns the verdict.

Stop at the first failure. We say the `experiment succeeds` when all stages succeed and verification accepts.

`K_P` counts program P's compressions in this experiment, including retries and failed attempts; it is zero if P is never reached. For each fixed seed and H, `Kmax_P` is the maximum of `K_P` over all messages. `BUDGET_P` denotes P's named budget.

1. **Success:** for every seed, `Pr_H[experiment succeeds for every message] >= 1 - FAILURE`.
2. **Compression budgets:** for every seed, `E_H[2^(Kmax_P / BUDGET_P)] <= 2` for each P in {`keygen`, `sign`, `expand`}.
3. **Verification cycles:** for every seed, message and oracle, if the experiment succeeds, `verify` uses at most `C` cycles.

`Pr_H` means the probability over H. `E_H` means the expected value over H.

### Security

Consider the following experiment for a classical probabilistic adversary `A` with unrestricted computation and an integer hash-call budget `Q >= 1`:

1. Sample H and a uniform seed independently. Initialize an empty transcript T and count all calls to H throughout the experiment.
2. Run `keygen(seed)`. Failure ends the experiment without a win; otherwise give `A` the public key and cache.
3. `A` may then adaptively query two oracles:
   - **`random_oracle(input_A)`:** return H(input_A).
   - **`signing_oracle(message_A, cache_A)`:** run `sign(seed, public key, cache_A, message_A)` using the original seed and public key. Return the signature or failure. Add each returned `(message_A, signature)` to T. Allow at most `LIFETIME` requests.
4. `A` makes one final submission, choosing either form below:
   - **witness weak unforgeability:** submit `(message_A, witness_A)`. `A` wins if `verify(message_A, public key, witness_A)` accepts, and no pair in T has message `message_A`, and the total hash-call count is at most Q
   - **signature strong unforgeability:** submit `(message_A, signature_A)`. `A` wins if `expand(message_A, public key, signature_A)` returns a witness that `verify` accepts, and `(message_A, signature_A)` is not in T, and the total hash-call count is at most Q.

The total hash-call count includes key generation, signing, `A`’s queries, and final expansion and verification when performed.

**Security:** for every A and `Q >= 1`, `Pr[A wins] <= Q / 2^SECURITY_BITS`, over the seed, H, and `A`’s private randomness.

### Program requirements

1. **Memory:** each program uses at most 16 MiB of memory.
2. **Termination:** every program terminates with a result or failure in fewer than `CYCLE_LIMIT` cycles, for every input and oracle.

## RISC-V interface

Use [RV64I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html) and the [M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).

Each program satisfies **`4 × instruction count + embedded-data bytes < 2^20`**, checked directly at submission.

### Code and memory

Code occupies a separate, immutable instruction address space. Instruction i is at `0x1000 + 4 × i`.

Memory occupies `0x000000`–`0xFFFFFF` (16 MiB), including embedded data, inputs, outputs, scratch space, and stack.

Initialize memory to zero. Load D embedded bytes at `data_base = 16 × floor((0x1000000 - D) / 16)`. Initially, `sp = data_base` and `PC = 0x1000`; all other integer registers are zero.

### Inputs and outputs

Inputs and outputs use the same addresses, fixed for each submission:

| Address                     | Buffer     |
| --------------------------- | ---------- |
| `0x00`                      | Message    |
| `0x20`                      | Seed       |
| `0x40`                      | Public key |
| `0x60`                      | Cache      |
| `0x20060`                   | Signature  |
| `0x20060 + 8 × ceil(S / 8)` | Witness    |

Load the inputs and read the outputs listed in the Programs table at their declared sizes. Other input fields start at zero.

HALT ends execution with `a0 = 1` for success, or `a0 = 0` for failure. For `verify`, these mean acceptance and rejection, respectively.

### System calls

ECALL selects one of two services through `t0`:

| `t0` | Service | Arguments                                                                |
| ---: | ------- | ------------------------------------------------------------------------ |
|    0 | HALT    | Status and outputs above                                                 |
|    1 | HASH    | `a0 = input address`, `a1 = input length in bits`, `a2 = output address` |

HASH writes H's 32-byte answer at the output address.

### Further Details

- **Proof checking:** the certificate must pass Lean’s kernel against the organizer’s definitions. Its transitive axiom dependencies may contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Instructions:** encodings are 32 bits. Fetching outside the code or at a non-4-byte-aligned address fails. `FENCE` has no effect; `EBREAK` fails.
- **Registers:** `x0`–`x31` are 64 bits. `x0` always reads zero and ignores writes. Aliases are `sp = x2`, `t0 = x5`, and `a0`–`a2 = x10`–`x12`. PC is separate.
- **Memory access:** addresses count bytes; multi-byte integers are little-endian. Loads and stores access only memory, not code. Accesses of 1, 2, 4, or 8 bytes require alignment to their size. Misaligned accesses fail.
- **Bounds:** every memory access and buffer must fit completely in memory. For unsigned byte address p and length n, require `p + n <= 0x1000000`. All size, layout, and bounds calculations use mathematical integers without overflow. Instruction arithmetic and effective-address calculation follow RV64IM.
- **Buffer layout:** cache, signature, and witness occupy separate consecutive areas, with up to seven alignment bytes after the signature. Require `0x20060 + 8 × ceil(S / 8) + W <= data_base` for each program.
- **Input loading:** reject incorrect sizes or buffers extending beyond `data_base`. Starting addresses are 8-byte aligned; lengths need not be multiples of eight.
- **Output extraction:** read each output at its declared size from its fixed address in final memory. On failure, ignore output buffers.
- **HASH arguments:** addresses and bit length n are unsigned 64-bit values. The input’s `ceil(n / 8)` bytes and the output’s 32 bytes must fit entirely in memory; check this before any oracle call or write. Both input and output addresses must be 8-byte aligned.
- **HASH execution:** read exactly n bits in increasing byte-address order, least-significant bit first within each byte; ignore unused high bits of the final byte. Read all input before writing the answer, so buffers may overlap. Preserve integer registers and advance PC by 4.
- **Faults:** unknown services, invalid arguments, invalid HALT statuses, invalid instruction encodings, and memory or instruction-fetch faults end the program with failure (`verify` rejects). Invalid fetches or encodings cost zero cycles; other faults cost one cycle and make no oracle call.

## Lean project

`SigGolf.Certificate submission C` in [SigGolf/Statements.lean](SigGolf/Statements.lean) is the competition claim for the exact four program images and declared sizes. [SigGolf/Security.lean](SigGolf/Security.lean) defines the attacker and both forgery experiments; [SigGolf/Riscv.lean](SigGolf/Riscv.lean) defines execution and costs.

Build the statements and regression checks with `lake build SigGolf SigGolfTests`. Dependencies are pinned in `lake-manifest.json`. These files define the requirements; they do not certify a particular signature scheme.
