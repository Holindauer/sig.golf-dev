import SigGolfCandidate.Hypertree.SignAdvance

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def captureModeInstructions (offset : BitVec 13) : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x440,
  .LD .x6 .x28 0,
  .BEQ .x6 .x0 offset]

def captureModeState (offset : BitVec 13) (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x440)
  let s := execInstrBr s (.LD .x6 .x28 0)
  execInstrBr s (.BEQ .x6 .x0 offset)

def captureModeCode (image : Image) (base : Word) (offset : BitVec 13) : Prop :=
  ∀ (s : MachineState) (i : Fin 4), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((captureModeInstructions offset)[i.val]'(by simp [captureModeInstructions])))

theorem captureMode_block (image : Image) (base : Word) (offset : BitVec 13)
    (code : captureModeCode image base offset) (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s 4 (captureModeState offset s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x440)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.BEQ .x6 .x0 offset)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 3
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x440)) 2
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.BEQ .x6 .x0 offset)) 0
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

def captureSelectorInstructions (offset : BitVec 13) : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x428,
  .LD .x6 .x28 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x420,
  .LD .x7 .x28 0,
  .BNE .x6 .x7 offset]

def captureSelectorState (offset : BitVec 13) (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x428)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x420)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 offset)

def captureSelectorCode (image : Image) (base : Word) (offset : BitVec 13) : Prop :=
  ∀ (s : MachineState) (i : Fin 7), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((captureSelectorInstructions offset)[i.val]'(by simp [captureSelectorInstructions])))

theorem captureSelector_block (image : Image) (base : Word) (offset : BitVec 13)
    (code : captureSelectorCode image base offset) (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s 7 (captureSelectorState offset s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x428)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x420)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.BNE .x6 .x7 offset)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 6
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x428)) 5
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 3
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x420)) 2
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 1
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.BNE .x6 .x7 offset)) 0
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

def captureWriteInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x510,
  .LD .x10 .x28 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x518,
  .LD .x11 .x28 0,
  .SD .x7 .x10 0,
  .SD .x7 .x11 8]

def captureWriteState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x510)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x518)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)

def captureWriteCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 8), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base ((captureWriteInstructions)[i.val]'(by simp [captureWriteInstructions])))

theorem captureWrite_block (image : Image) (base : Word)
    (code : captureWriteCode image base) (s : MachineState) (pc : s.pc = base)
    (safe : accessValid (s.getReg .x7) 8 = true)
    (safeNext : accessValid (s.getReg .x7 + 8) 8 = true) :
    OrdinarySteps image s 8 (captureWriteState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x510)
  let s3 := execInstrBr s2 (.LD .x10 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x518)
  let s6 := execInstrBr s5 (.LD .x11 .x28 0)
  let s7 := execInstrBr s6 (.SD .x7 .x10 0)
  let s8 := execInstrBr s7 (.SD .x7 .x11 8)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 7
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x510)) 6
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x10 .x28 0)) 5
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 4
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x518)) 3
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x11 .x28 0)) 2
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x7 .x10 0)) 1
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, safe, safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x11 8)) 0
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, safe, safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safeNext
  exact OrdinarySteps.refl _

theorem captureMode_pc (offset : BitVec 13) (s : MachineState) :
    (captureModeState offset s).pc = if s.getMem 0x80440 = 0 then
      s.pc + 12 + signExtend13 offset else s.pc + 16 := by
  simp [captureModeState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]

theorem captureMode_mem (offset : BitVec 13) (s : MachineState) (a : Word) :
    (captureModeState offset s).getMem a = s.getMem a := by
  simp [captureModeState, execInstrBr]

theorem captureMode_sp (offset : BitVec 13) (s : MachineState) :
    (captureModeState offset s).getReg .x2 = s.getReg .x2 := by
  simp [captureModeState, execInstrBr, MachineState.getReg_setReg_ne]

theorem captureSelector_pc (offset : BitVec 13) (s : MachineState) :
    (captureSelectorState offset s).pc = if s.getMem 0x80428 = s.getMem 0x80420 then
      s.pc + 28 else s.pc + 24 + signExtend13 offset := by
  simp [captureSelectorState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]

theorem captureSelector_mem (offset : BitVec 13) (s : MachineState) (a : Word) :
    (captureSelectorState offset s).getMem a = s.getMem a := by
  simp [captureSelectorState, execInstrBr]

theorem captureSelector_sp (offset : BitVec 13) (s : MachineState) :
    (captureSelectorState offset s).getReg .x2 = s.getReg .x2 := by
  simp [captureSelectorState, execInstrBr, MachineState.getReg_setReg_ne]

theorem captureWrite_pc (s : MachineState) : (captureWriteState s).pc = s.pc + 32 := by
  simp [captureWriteState, execInstrBr, BitVec.add_assoc]

theorem captureWrite_mem (s : MachineState) (a : Word) :
    (captureWriteState s).getMem a = if a = s.getReg .x7 + 8 then s.getMem 0x80518 else
      if a = s.getReg .x7 then s.getMem 0x80510 else s.getMem a := by
  simp [captureWriteState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem captureWrite_sp (s : MachineState) :
    (captureWriteState s).getReg .x2 = s.getReg .x2 := by
  simp [captureWriteState, execInstrBr, MachineState.getReg_setReg_ne]

/-- Key generation executes exactly the four-instruction disabled-capture guard. -/
theorem capture_disabled (image : Image) (base : Word) (offset : BitVec 13)
    (code : captureModeCode image base offset) (s : MachineState) (pc : s.pc = base)
    (disabled : s.getMem 0x80440 = 0) :
    ∃ final, OrdinarySteps image s 4 final ∧
      final.pc = base + 12 + signExtend13 offset ∧
      (∀ a, final.getMem a = s.getMem a) ∧ final.getReg .x2 = s.getReg .x2 := by
  refine ⟨captureModeState offset s, captureMode_block image base offset code s pc, ?_,
    captureMode_mem offset s, captureMode_sp offset s⟩
  rw [captureMode_pc, if_pos disabled, pc]


theorem sign_upper_mode_code : captureModeCode sign 0x1698 128 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_upper_selector_code : captureSelectorCode sign 0x16a8 100 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_upper_write_code : captureWriteCode sign 0x1704 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_bottom_mode_code : captureModeCode sign 0x1ae0 76 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_bottom_selector_code : captureSelectorCode sign 0x1af0 48 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_bottom_write_code : captureWriteCode sign 0x1b18 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_mode_code : captureModeCode keygen 0x1318 128 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_selector_code : captureSelectorCode keygen 0x1328 100 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_upper_write_code : captureWriteCode keygen 0x1384 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_bottom_mode_code : captureModeCode keygen 0x1760 76 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_bottom_selector_code : captureSelectorCode keygen 0x1770 48 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_bottom_write_code : captureWriteCode keygen 0x1798 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.Signing
