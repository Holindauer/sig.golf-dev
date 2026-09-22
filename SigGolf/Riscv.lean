import SigGolf.Oracle
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode

/-! The beta execution environment reuses ots.golf's pinned RV64 register and arithmetic model. Memory permissions, raw instruction images, missing word instructions, and system calls are defined here. -/

namespace SigGolf.Riscv
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter OracleComp OracleSpec

structure Image where
  code : List (BitVec 32)
  data : List Byte
  deriving Repr

def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length

def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)
def signatureBase : Nat := 0x20060
def witnessBase (sizes : Sizes) : Nat := signatureBase + 8 * ((sizes.signature + 7) / 8)

def Image.Valid (image : Image) (sizes : Sizes) : Prop :=
  image.byteSize < MEMORY_BYTES ∧ witnessBase sizes + sizes.witness ≤ dataBase image

instance (image : Image) (sizes : Sizes) : Decidable (image.Valid sizes) :=
  inferInstanceAs (Decidable (image.byteSize < MEMORY_BYTES ∧ witnessBase sizes + sizes.witness ≤ dataBase image))

def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)

def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)

/-- Extensions needed to cover the complete RV64IM word-operation family. -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq, Repr

inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)
  deriving Repr

/-- The program contains actual 32-bit encodings, never assembler pseudo-instructions. -/
def decodeInstruction (word : BitVec 32) : Option Instruction := do
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x73 then
    if word = 0x00000073 then return .base .ECALL
    else if word = 0x00100073 then return .base .EBREAK
    else none
  else if opcode = 0x3b then
    let op ← match f7, f3 with
      | 0, 0 => some WordOp.add
      | 0x20, 0 => some .sub
      | 0, 1 => some .sll
      | 0, 5 => some .srl
      | 0x20, 5 => some .sra
      | 1, 0 => some .mul
      | 1, 4 => some .div
      | 1, 5 => some .divu
      | 1, 6 => some .rem
      | 1, 7 => some .remu
      | _, _ => none
    return .word op rd rs1 rs2
  else if opcode = 0x1b && f3 = 5 && f7 = 0x20 then
    return .sraiw rd rs1 (word.extractLsb' 20 5)
  else
    return .base (← RiscvZkvm.Interpreter.decode word)

def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b

/-- All data accesses use beta's complete byte-range checks, including address zero. -/
def memoryArgumentsValid (state : MachineState) : Instr → Bool
  | .LB _ rs off | .LBU _ rs off | .SB rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 1
  | .LH _ rs off | .LHU _ rs off | .SH rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 2
  | .LW _ rs off | .LWU _ rs off | .SW rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 4
  | .LD _ rs off | .SD rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 8
  | _ => true

def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base (.ECALL) | .base (.EBREAK) | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base (.NOP) => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))

def fetch (image : Image) (state : MachineState) : Option Instruction := do
  if state.pc.toNat < 0x1000 || state.pc.toNat % 4 != 0 then none else
    let word ← image.code[(state.pc.toNat - 0x1000) / 4]?
    decodeInstruction word

def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bits := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && rangeValid source ((bits + 7) / 8) &&
    accessValid destination 8 && rangeValid destination 32

def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat
  ⟨n, BitVec.ofNat n ((List.range n).foldl (fun acc i =>
    acc + if (state.getByte (state.getReg .x10 + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
      then 2 ^ i else 0) 0)⟩

def writeHash (state : MachineState) (answer : BitVec 256) : MachineState :=
  (state.writeWords (state.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
      answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (state.pc + 4)

inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq, Repr

structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat := 0
  hashCalls : Nat := 0
  hashCompressions : Nat := 0

def Execution.charge (result : Execution) (cycles hashes blocks : Nat) : Execution :=
  { result with
    cycles := cycles + result.cycles
    hashCalls := hashes + result.hashCalls
    hashCompressions := blocks + result.hashCompressions }

/-- Fuel is a logical observation depth, not a VM timeout. Certification must exclude `unfinished` for every fixed oracle. -/
def execute : Nat → Image → MachineState → OracleComp HashSpec Execution
  | 0, _, state => pure ⟨.unfinished, state, 0, 0, 0⟩
  | fuel + 1, image, state =>
    match fetch image state with
    | none => pure ⟨.failure, state, 0, 0, 0⟩
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 then
        pure ⟨if state.getReg .x10 = 1 then .success else .failure, state, 1, 0, 0⟩
      else if state.getReg .x5 = 1 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute fuel image (writeHash state answer)
        return result.charge (8 * compressions input.1) 1 (compressions input.1)
      else pure ⟨.failure, state, 1, 0, 0⟩
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure ⟨.failure, state, 1, 0, 0⟩
      | some next => (fun result => result.charge 1 0 0) <$> execute fuel image next

end SigGolf.Riscv
