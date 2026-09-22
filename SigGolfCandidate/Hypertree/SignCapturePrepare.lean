import SigGolfCandidate.Hypertree.SignCapture

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def capturePointerInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x448,
  .LD .x7 .x28 0]

def capturePointerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  execInstrBr s (.LD .x7 .x28 0)

def capturePointerCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 3), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((capturePointerInstructions)[i.val]'(by simp [capturePointerInstructions])))

theorem capturePointer_block (image : Image) (base : Word)
    (code : capturePointerCode image base) (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s 3 (capturePointerState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x448)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 2
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x448)) 1
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 0
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem capturePointer_mem (s : MachineState) (a : Word) :
    (capturePointerState s).getMem a = s.getMem a := by
  simp [capturePointerState, execInstrBr]

theorem capturePointer_sp (s : MachineState) :
    (capturePointerState s).getReg .x2 = s.getReg .x2 := by
  simp [capturePointerState, execInstrBr, MachineState.getReg_setReg_ne]

def captureDigitInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x430,
  .LD .x6 .x28 0,
  .LUI .x10 0x80,
  .ADDI .x10 .x10 0x600,
  .ADD .x10 .x10 .x6,
  .LBU .x10 .x10 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x438,
  .LD .x11 .x28 0,
  .BNE .x10 .x11 44]

def captureDigitState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x430)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0x600)
  let s := execInstrBr s (.ADD .x10 .x10 .x6)
  let s := execInstrBr s (.LBU .x10 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  let s := execInstrBr s (.LD .x11 .x28 0)
  execInstrBr s (.BNE .x10 .x11 44)

def captureDigitCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 11), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((captureDigitInstructions)[i.val]'(by simp [captureDigitInstructions])))

theorem captureDigit_block (image : Image) (base : Word)
    (code : captureDigitCode image base) (s : MachineState) (pc : s.pc = base)
    (safe : accessValid (0x80600 + s.getMem 0x80430) 1 = true) :
    OrdinarySteps image s 11 (captureDigitState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x430)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x10 0x80)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 0x600)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x6)
  let s7 := execInstrBr s6 (.LBU .x10 .x10 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x80)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0x438)
  let s10 := execInstrBr s9 (.LD .x11 .x28 0)
  let s11 := execInstrBr s10 (.BNE .x10 .x11 44)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 10
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x430)) 9
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x10 0x80)) 7
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x10 0x600)) 6
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x6)) 5
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LBU .x10 .x10 0)) 4
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, safe, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safe
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x80)) 3
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0x438)) 2
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x11 .x28 0)) 1
  · apply code _ 9
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.BNE .x10 .x11 44)) 0
  · apply code _ 10
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem captureDigit_mem (s : MachineState) (a : Word) :
    (captureDigitState s).getMem a = s.getMem a := by
  simp [captureDigitState, execInstrBr]

theorem captureDigit_sp (s : MachineState) :
    (captureDigitState s).getReg .x2 = s.getReg .x2 := by
  simp [captureDigitState, execInstrBr, MachineState.getReg_setReg_ne]

def capturePositionInstructions : List Instr := [
  .SLLI .x6 .x6 4,
  .ADD .x7 .x7 .x6]

def capturePositionState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SLLI .x6 .x6 4)
  execInstrBr s (.ADD .x7 .x7 .x6)

def capturePositionCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 2), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((capturePositionInstructions)[i.val]'(by simp [capturePositionInstructions]; omega)))

theorem capturePosition_block (image : Image) (base : Word)
    (code : capturePositionCode image base) (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s 2 (capturePositionState s) := by
  let s1 := execInstrBr s (.SLLI .x6 .x6 4)
  let s2 := execInstrBr s1 (.ADD .x7 .x7 .x6)
  apply OrdinarySteps.step s s1 _ (.base (.SLLI .x6 .x6 4)) 1
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x7 .x7 .x6)) 0
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem capturePosition_mem (s : MachineState) (a : Word) :
    (capturePositionState s).getMem a = s.getMem a := by
  simp [capturePositionState, execInstrBr]

theorem capturePosition_sp (s : MachineState) :
    (capturePositionState s).getReg .x2 = s.getReg .x2 := by
  simp [capturePositionState, execInstrBr, MachineState.getReg_setReg_ne]

theorem capturePointer_pc (s : MachineState) : (capturePointerState s).pc = s.pc + 12 := by
  simp [capturePointerState, execInstrBr, BitVec.add_assoc]

theorem capturePointer_reg (s : MachineState) :
    (capturePointerState s).getReg .x7 = s.getMem 0x80448 := by
  simp [capturePointerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem captureDigit_regs (s : MachineState) :
    (captureDigitState s).getReg .x6 = s.getMem 0x80430 ∧
    (captureDigitState s).getReg .x7 = s.getReg .x7 := by
  simp [captureDigitState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem captureDigit_pc (s : MachineState) :
    (captureDigitState s).pc =
      if (s.getByte (0x80600 + s.getMem 0x80430)).zeroExtend 64 = s.getMem 0x80438
      then s.pc + 44 else s.pc + 84 := by
  simp [captureDigitState, execInstrBr, MachineState.getByte, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]
  rfl

theorem capturePosition_pc (s : MachineState) : (capturePositionState s).pc = s.pc + 8 := by
  simp [capturePositionState, execInstrBr, BitVec.add_assoc]

theorem capturePosition_reg (s : MachineState) :
    (capturePositionState s).getReg .x7 = s.getReg .x7 + (s.getReg .x6 <<< 4) := by
  simp [capturePositionState, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]


theorem sign_upper_pointer_code : capturePointerCode sign 0x16c4 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_upper_digit_code : captureDigitCode sign 0x16d0 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_upper_position_code : capturePositionCode sign 0x16fc := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_bottom_pointer_code : capturePointerCode sign 0x1b0c := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_pointer_code : capturePointerCode keygen 0x1344 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_digit_code : captureDigitCode keygen 0x1350 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_position_code : capturePositionCode keygen 0x137c := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_bottom_pointer_code : capturePointerCode keygen 0x178c := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.Signing
