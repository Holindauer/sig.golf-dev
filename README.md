# sig.golf · beta rules

Design a **stateless hash-based signature scheme** minimizing `S × C`: signature bytes times maximum honest verification cycles.

## Submission

1. Four RISC-V program images: [keygen](#keygen), [sign](#sign), [expand](#expand), and [verify](#verify), including embedded data.
2. Nonnegative integers `S`, `W`, and `C`: signature bytes, witness bytes, and verification cycles.
3. [Six byte offsets](#inputs-and-outputs) specifying where RISC-V inputs and outputs reside in memory.
4. Lean 4 proofs of the [required statements](#required-lean-statements) for those exact images, sizes, layout, and bound.

## Parameters

| Constant          |                 Value |
| ----------------- | --------------------: |
| `BUDGET_KEYGEN`   |     2^20 compressions |
| `BUDGET_SIGN`     |     2^17 compressions |
| `BUDGET_EXPAND`   |     2^20 compressions |
| `FAILURE`         |                2^-256 |
| `LIFETIME`        | 2^32 signing requests |
| `SECURITY_BITS`   |                   127 |
| `CYCLE_LIMIT`     |           2^32 cycles |
| `MAX_IMAGE_BYTES` |            2^20 bytes |

Every object has a fixed size in bytes:

| Object            |                Bytes |
| ----------------- | -------------------: |
| Message    |                   32 |
| Secret key        |                   32 |
| Public key        |                   16 |
| Cache             |       2^17 (128 KiB) |
| Signature |              `S` ≥ 1 |
| Witness  | `W` ≤ 2^17 (128 KiB) |

## Programs

### keygen

Derives the public key and a public, untrusted cache from the secret key.

- **Inputs:** secret key.
- **Outputs:** public key and cache, or failure.
- **Context:** enclave.

### sign

Produces a compact signature for a given message.

- **Inputs:** secret key, public key, cache, message.
- **Outputs:** signature or failure.
- **Context:** enclave.

### expand

Converts the signature into a verification witness.

Example: It may restore pruned Merkle paths or copy the signature when `S = W`.

- **Inputs:** message, public key, signature.
- **Outputs:** witness or failure.
- **Context:** prover host.

### verify

Checks whether the witness authenticates the message under the public key.

- **Inputs:** message, public key, witness.
- **Outputs:** accept or reject.
- **Context:** zkVM.

## Model and costs

All programs and the adversary share a random oracle H.

Security counts calls to H. Program budgets and HASH cycles count compressions: hashing n bits costs `max(1, ⌈n / 512⌉)` compressions.

RiscV cycle breakdown:

| Operation            | Cost                                                   |
| -------------------- | ------------------------------------------------------ |
| Ordinary instruction | 1 cycle                                                |
| HASH                 | 8 cycles per compression (no extra instruction charge) |
| HALT                 | 1 cycle                                                |

## Required Lean statements

### Completeness

For any `secretKey`, `message` and oracle H, consider the following experiment:

1. `keygen(secretKey)` returns the `public key` and `cache`.
2. `sign(secretKey, public key, cache, message)` returns the `signature`.
3. `expand(message, public key, signature)` returns the `witness`.
4. `verify(message, public key, witness)` returns the verdict.

Stop at the first failure. We say the `experiment succeeds` when all stages succeed and verification accepts.

`K_P` counts program P's compressions; it is zero if P is never reached. `BUDGET_P` denotes P's named budget.

1. **Success:** for every secret key, `Pr_H[experiment succeeds for every message] >= 1 - FAILURE`.
2. **Compression budgets:** for every secret key and P in {`keygen`, `sign`, `expand`}, `E_{H,M}[2^(K_P / BUDGET_P)] <= 2`.

`Pr_H` is over H; `E_{H,M}` is over an independently sampled random oracle H and uniform 32-byte message M. Attacker-chosen messages or altered caches/signatures may cost more. TODO: Can we improve this?

3. **Verification cycles:** for every secret key, message and oracle, if the experiment succeeds, `verify` uses at most `C` cycles.

### Security

Consider the following experiment for a classical probabilistic adversary `A` with unrestricted computation and an integer hash-call budget `Q >= 1`:

1. Sample H and a uniform secret key independently. Initialize an empty transcript T and count all calls to H throughout the experiment.
2. Run `keygen(secretKey)`. Failure ends the experiment without a win; otherwise give `A` the public key and cache.
3. `A` may then adaptively query two oracles:
   - **`random_oracle(input_A)`:** return H(input_A).
   - **`signing_oracle(message_A, cache_A)`:** run `sign(secretKey, public key, cache_A, message_A)` using the original secret key and public key. Return the signature or failure. Add each returned `(message_A, signature)` to T. Allow at most `LIFETIME` requests.
4. `A` makes one final submission, choosing either form below:
   - **witness weak unforgeability:** submit `(message_A, witness_A)`. `A` wins if `verify(message_A, public key, witness_A)` accepts, and no pair in T has message `message_A`, and the total hash-call count is at most Q
   - **signature strong unforgeability:** submit `(message_A, signature_A)`. `A` wins if `expand(message_A, public key, signature_A)` returns a witness that `verify` accepts, and `(message_A, signature_A)` is not in T, and the total hash-call count is at most Q.

The total hash-call count includes key generation, signing, `A`’s queries, and final expansion and verification when performed.

**Security:** for every A and `Q >= 1`, `Pr[A wins] <= Q / 2^SECURITY_BITS`, over the secret key, H, and `A`’s private randomness.

### Program requirements

1. **Termination:** every program terminates with a result or failure in fewer than `CYCLE_LIMIT` cycles, for every input and oracle.

## RISC-V interface

Use [RV64I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html) and the [M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).

Each program satisfies **`4 × instruction count + embedded-data bytes < MAX_IMAGE_BYTES`**, checked directly at submission.

### Code and memory

Code occupies a separate, immutable instruction address space. Instruction i is at `0x1000 + 4 × i`.

Memory occupies `0x000000`–`0xFFFFFF` (16 MiB), including embedded data, inputs, outputs, scratch space, and stack. The verifier enforces this range directly; it is not a separate Lean proof obligation.

Load D embedded bytes at `data_base = 16 × floor((0x1000000 - D) / 16)`. Initially, `sp = data_base` and `PC = 0x1000`; all other integer registers are zero.

### Inputs and outputs

Each submission specifies six byte offsets, shared by all four programs: δ<sub>message</sub>, δ<sub>secret key</sub>, δ<sub>public key</sub>, δ<sub>cache</sub>, δ<sub>signature</sub>, and δ<sub>witness</sub>. Each gives the memory address where that object is written or read. The buffers have the sizes in [Parameters](#parameters), start at 8-byte-aligned addresses, do not overlap, and end at or below `data_base` for every program.

Before each execution, memory is zero except for embedded data and the inputs listed under [Programs](#programs); unused object buffers remain zero. For example, before [`sign`](#sign), write the secret key, public key, cache, and message at their offsets. On success, read the signature at δ<sub>signature</sub>.

HALT ends execution with `a0 = 1` for success, or `a0 = 0` for failure. For [`verify`](#verify), these mean acceptance and rejection, respectively.

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
- **HASH arguments:** addresses and bit length n are unsigned 64-bit values. The input’s `ceil(n / 8)` bytes and the output’s 32 bytes must fit entirely in memory; check this before any oracle call or write. Both input and output addresses must be 8-byte aligned.
- **HASH execution:** read exactly n bits in increasing byte-address order, least-significant bit first within each byte; ignore unused high bits of the final byte. Read all input before writing the answer, so buffers may overlap. Preserve integer registers and advance PC by 4.

## Lean project

`SigGolf.Certificate submission C` in [SigGolf/Statements.lean](SigGolf/Statements.lean) is the competition claim for the exact four program images and declared sizes. [SigGolf/Security.lean](SigGolf/Security.lean) defines the attacker and both forgery experiments; [SigGolf/Riscv.lean](SigGolf/Riscv.lean) defines execution and costs.

Build the statements and regression checks with `lake build SigGolf SigGolfTests`. Dependencies are pinned in `lake-manifest.json`. These files define the requirements; they do not certify a particular signature scheme.
