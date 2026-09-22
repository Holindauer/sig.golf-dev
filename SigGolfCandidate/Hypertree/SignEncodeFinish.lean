import SigGolfCandidate.Hypertree.SignEncodeLoop
import SigGolfCandidate.Hypertree.KeygenControl

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

@[simp] theorem reg_setByte (s : MachineState) (a : Word) (b : Byte) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by simp [MachineState.setByte]

@[simp] theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by simp [MachineState.getByte]

def checksumState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 0)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 1)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 2)
  execInstrBr s (.SRLI .x12 .x12 3)

def checksumInstructions : List Instr := [
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 0,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 1,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 2,
  .SRLI .x12 .x12 3]

def ChecksumCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 9), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (checksumInstructions[i.val]'(by simp [checksumInstructions])))

theorem checksumState_block (image : Image) (base : Word) (code : ChecksumCode image base)
    (s : MachineState) (pc : s.pc = base) (ptr : s.getReg .x10 = 0x8062b) :
    OrdinarySteps image s 9 (checksumState s) := by
  let s1 := execInstrBr s (.ANDI .x13 .x12 7)
  let s2 := execInstrBr s1 (.SB .x10 .x13 0)
  let s3 := execInstrBr s2 (.SRLI .x12 .x12 3)
  let s4 := execInstrBr s3 (.ANDI .x13 .x12 7)
  let s5 := execInstrBr s4 (.SB .x10 .x13 1)
  let s6 := execInstrBr s5 (.SRLI .x12 .x12 3)
  let s7 := execInstrBr s6 (.ANDI .x13 .x12 7)
  let s8 := execInstrBr s7 (.SB .x10 .x13 2)
  let s9 := execInstrBr s8 (.SRLI .x12 .x12 3)
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x13 .x12 7)) 8
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SB .x10 .x13 0)) 7
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SRLI .x12 .x12 3)) 6
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x13 .x12 7)) 5
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SB .x10 .x13 1)) 4
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.SRLI .x12 .x12 3)) 3
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ANDI .x13 .x12 7)) 2
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SB .x10 .x13 2)) 1
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.SRLI .x12 .x12 3)) 0
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem checksumState_pc (s : MachineState) : (checksumState s).pc = s.pc + 36 := by
  simp [checksumState, execInstrBr, BitVec.add_assoc]

theorem checksumState_sp (s : MachineState) : (checksumState s).getReg .x2 = s.getReg .x2 := by
  simp [checksumState, execInstrBr, MachineState.getReg_setReg_ne]

theorem checksumState_byte (s : MachineState) (a : Word) :
    (checksumState s).getByte a =
      if a = s.getReg .x10 + 2 then ((s.getReg .x12 >>> 6) &&& 7).truncate 8 else
      if a = s.getReg .x10 + 1 then ((s.getReg .x12 >>> 3) &&& 7).truncate 8 else
      if a = s.getReg .x10 then (s.getReg .x12 &&& 7).truncate 8 else s.getByte a := by
  simp [checksumState, execInstrBr, signExtend12, getByte_setByte, Memory.getByte_setReg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ← BitVec.shiftRight_add]

theorem checksum_digit (checksum : Nat) (bound : checksum ≤ 301) (i : Fin 3) :
    ((BitVec.ofNat 64 checksum >>> (3 * i.val)) &&& 7).truncate 8 =
      BitVec.ofNat 8 (checksum / 8 ^ i.val % 8) := by
  apply BitVec.eq_of_toNat_eq
  have small : checksum < 2 ^ 64 := by omega
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.shiftRight_eq_div_pow]
  change (checksum / 2 ^ (3 * i.val) &&& 7) % 2 ^ 8 = _
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  fin_cases i <;> simp

theorem sign_checksum_code : ChecksumCode sign 0x1398 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem verify_checksum_code : ChecksumCode verify 0x12c0 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem checksumState_output (s : MachineState) (checksum : Nat) (bound : checksum ≤ 301)
    (ptr : s.getReg .x10 = 0x8062b) (value : s.getReg .x12 = BitVec.ofNat 64 checksum)
    (i : Fin 3) :
    (checksumState s).getByte (BitVec.ofNat 64 (0x8062b + i.val)) =
      BitVec.ofNat 8 (checksum / 8 ^ i.val % 8) := by
  fin_cases i
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 0
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 1
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 2

theorem checksumState_frame (s : MachineState) (ptr : s.getReg .x10 = 0x8062b)
    (a : Word) (outside : ∀ i : Fin 3, a ≠ BitVec.ofNat 64 (0x8062b + i.val)) :
    (checksumState s).getByte a = s.getByte a := by
  have h0 : a ≠ 0x8062b := outside 0
  have h1 : a ≠ 0x8062c := outside 1
  have h2 : a ≠ 0x8062d := outside 2
  rw [checksumState_byte, ptr]
  change (if a = 0x8062d then _ else if a = 0x8062c then _ else if a = 0x8062b then _ else _) = _
  rw [if_neg h2, if_neg h1, if_neg h0]

theorem digit_address_ne (i j : Nat) (hi : i < 46) (hj : j < 46) (ne : i ≠ j) :
    BitVec.ofNat 64 (0x80600 + i) ≠ BitVec.ofNat 64 (0x80600 + j) := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have h1 : 0x80600 + i < 2 ^ 64 := by omega
  have h2 : 0x80600 + j < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at values
  omega

/-- Completing the three checksum digits yields every one of the reference's 46 digits. -/
theorem checksumState_refines (s : MachineState) (message : Reference.Digest)
    (ptr : s.getReg .x10 = 0x8062b)
    (value : s.getReg .x12 = BitVec.ofNat 64 (Reference.checksum message))
    (digits : ∀ i : Fin 43, s.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
      BitVec.ofNat 8 (Reference.messageDigit message i)) :
    ∀ i : Reference.Chain, (checksumState s).getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
      BitVec.ofNat 8 (Reference.digit message i).val := by
  intro i
  by_cases small : i.val < 43
  · rw [checksumState_frame s ptr, digits ⟨i.val, small⟩]
    · simp [Reference.digit, Reference.messageDigit, small]
    · intro j
      have hj := j.isLt
      have eq : 0x8062b + j.val = 0x80600 + (43 + j.val) := by omega
      rw [eq]
      exact digit_address_ne i.val (43 + j.val) i.isLt (by omega) (by omega)
  · have hj : i.val - 43 < 3 := by have := i.isLt; omega
    have bound : Reference.checksum message ≤ 301 := Nat.sub_le _ _
    have output := checksumState_output s (Reference.checksum message) bound ptr value ⟨i.val - 43, hj⟩
    have addr : 0x8062b + (i.val - 43) = 0x80600 + i.val := by omega
    simpa [addr, Reference.digit, small] using output

end SigGolfCandidate.Hypertree.Signing
