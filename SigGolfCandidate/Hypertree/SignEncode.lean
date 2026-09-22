import SigGolfCandidate.Hypertree.SignShift
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Exact byte-store semantics, including other bytes in the same containing word. -/
theorem getByte_setByte (s : MachineState) (address : Word) (b : Byte) (a : Word) :
    (s.setByte address b).getByte a = if a = address then b else s.getByte a := by
  by_cases same : a = address
  · subst a
    simp only [MachineState.getByte, MachineState.setByte, mem_setMem, if_pos rfl]
    exact extractByte_replaceByte_same _ ⟨byteOffset address, byteOffset_lt_8⟩ b
  · rw [if_neg same]
    simp only [MachineState.getByte, MachineState.setByte, mem_setMem]
    by_cases aligned : alignToDword a = alignToDword address
    · rw [if_pos aligned]
      have offset : byteOffset a ≠ byteOffset address := by
        intro eq
        apply same
        rw [← alignToDword_add_byteOffset a, ← alignToDword_add_byteOffset address, aligned, eq]
      rw [extractByte_replaceByte_diff _ _ (byteOffset_lt_8) (byteOffset_lt_8) offset, aligned]
    · rw [if_neg aligned]

def encodeNext (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ANDI .x13 .x6 7)
  let s := execInstrBr s (.SB .x10 .x13 0)
  let s := execInstrBr s (.SUB .x12 .x12 .x13)
  let s := execInstrBr s (.SRLI .x6 .x6 3)
  let s := execInstrBr s (.SLLI .x13 .x7 61)
  let s := execInstrBr s (.ADD .x6 .x6 .x13)
  let s := execInstrBr s (.SRLI .x7 .x7 3)
  let s := execInstrBr s (.ADDI .x10 .x10 1)
  let s := execInstrBr s (.ADDI .x11 .x11 (-1))
  execInstrBr s (.BNE .x11 .x0 (-36))

def encodeLoopInstructions : List Instr := [
  .ANDI .x13 .x6 7,
  .SB .x10 .x13 0,
  .SUB .x12 .x12 .x13,
  .SRLI .x6 .x6 3,
  .SLLI .x13 .x7 61,
  .ADD .x6 .x6 .x13,
  .SRLI .x7 .x7 3,
  .ADDI .x10 .x10 1,
  .ADDI .x11 .x11 (-1),
  .BNE .x11 .x0 (-36)]

def EncodeLoopCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 10), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (encodeLoopInstructions[i.val]'(by simp [encodeLoopInstructions])))

theorem encodeNext_block (image : Image) (base : Word) (code : EncodeLoopCode image base)
    (s : MachineState) (pc : s.pc = base)
    (valid : accessValid (s.getReg .x10) 1 = true) :
    OrdinarySteps image s 10 (encodeNext s) := by
  let s1 := execInstrBr s (.ANDI .x13 .x6 7)
  let s2 := execInstrBr s1 (.SB .x10 .x13 0)
  let s3 := execInstrBr s2 (.SUB .x12 .x12 .x13)
  let s4 := execInstrBr s3 (.SRLI .x6 .x6 3)
  let s5 := execInstrBr s4 (.SLLI .x13 .x7 61)
  let s6 := execInstrBr s5 (.ADD .x6 .x6 .x13)
  let s7 := execInstrBr s6 (.SRLI .x7 .x7 3)
  let s8 := execInstrBr s7 (.ADDI .x10 .x10 1)
  let s9 := execInstrBr s8 (.ADDI .x11 .x11 (-1))
  let s10 := execInstrBr s9 (.BNE .x11 .x0 (-36))
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x13 .x6 7)) 9
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SB .x10 .x13 0)) 8
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, valid, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SUB .x12 .x12 .x13)) 7
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SRLI .x6 .x6 3)) 6
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x13 .x7 61)) 5
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x6 .x6 .x13)) 4
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SRLI .x7 .x7 3)) 3
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x10 .x10 1)) 2
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x11 (-1))) 1
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.BNE .x11 .x0 (-36))) 0
  · apply code _ 9
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem encodeNext_regs (s : MachineState) :
    (encodeNext s).getReg .x6 = (s.getReg .x6 >>> 3) + (s.getReg .x7 <<< 61) ∧
    (encodeNext s).getReg .x7 = s.getReg .x7 >>> 3 ∧
    (encodeNext s).getReg .x10 = s.getReg .x10 + 1 ∧
    (encodeNext s).getReg .x11 = s.getReg .x11 - 1 ∧
    (encodeNext s).getReg .x12 = s.getReg .x12 - (s.getReg .x6 &&& 7) := by
  simp [encodeNext, execInstrBr, signExtend12, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.sub_eq_add_neg]

theorem encodeNext_mem (s : MachineState) (a : Word) :
    (encodeNext s).getMem a =
      (s.setByte (s.getReg .x10) ((s.getReg .x6 &&& 7).truncate 8)).getMem a := by
  simp [encodeNext, execInstrBr, signExtend12, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem encodeNext_byte (s : MachineState) (a : Word) :
    (encodeNext s).getByte a =
      if a = s.getReg .x10 then (s.getReg .x6 &&& 7).truncate 8 else s.getByte a := by
  have eq : (encodeNext s).getByte a =
      (s.setByte (s.getReg .x10) ((s.getReg .x6 &&& 7).truncate 8)).getByte a := by
    simp only [MachineState.getByte, encodeNext_mem]
  rw [eq, getByte_setByte]

theorem encodeNext_pc (s : MachineState) :
    (encodeNext s).pc = if s.getReg .x11 = 1 then s.pc + 40 else s.pc := by
  have decrement (x : Word) : x - 1#64 = 0#64 ↔ x = 1#64 :=
    BitVec.sub_left_inj (x := x) (y := 1) 1
  simp [encodeNext, execInstrBr, signExtend12, signExtend13, MachineState.setByte, BitVec.add_assoc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.sub_eq_add_neg,
    ← BitVec.sub_eq_add_neg, decrement]
  have hm : 18446744073709551615#64 = -1#64 := by decide
  rw [hm, ← BitVec.sub_eq_add_neg]
  simp only [decrement]

/-- info: 'SigGolfCandidate.Hypertree.Signing.encodeNext_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encodeNext_block

theorem sign_encode_loop_code : EncodeLoopCode sign 0x1370 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem verify_encode_loop_code : EncodeLoopCode verify 0x1298 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem encodeNext_sp (s : MachineState) : (encodeNext s).getReg .x2 = s.getReg .x2 := by
  simp [encodeNext, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.Signing
