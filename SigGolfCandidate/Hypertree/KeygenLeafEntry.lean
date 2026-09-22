import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.KeygenLeafEntry

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) (offset : BitVec 13) : Prop :=
  instructionAt image (p + 0) = some (.base (.ADDI .x6 .x0 0)) ∧
  instructionAt image (p + 4) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 8) = some (.base (.ADDI .x28 .x28 1072)) ∧
  instructionAt image (p + 12) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x6 .x0 0)) ∧
  instructionAt image (p + 20) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 24) = some (.base (.ADDI .x28 .x28 1080)) ∧
  instructionAt image (p + 28) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 32) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 36) = some (.base (.ADDI .x28 .x28 1024)) ∧
  instructionAt image (p + 40) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 44) = some (.base (.BEQ .x6 .x0 offset))

instance (image : Image) (p : Word) (offset : BitVec 13) : Decidable (Code image p offset) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) (offset : BitVec 13) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1072)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1080)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1024)
  let s := execInstrBr s (.LD .x6 .x28 0)
  execInstrBr s (.BEQ .x6 .x0 offset)

theorem block (image : Image) (p : Word) (offset : BitVec 13) (code : Code image p offset)
    (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 12 (state s offset) := by

  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11⟩ := code
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 1072)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 128)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 1080)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.LUI .x28 128)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 1024)
  let s11 := execInstrBr s10 (.LD .x6 .x28 0)
  let s12 := execInstrBr s11 (.BEQ .x6 .x0 offset)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 11
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 10
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 1072)) 9
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 8
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 7
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 128)) 6
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 1080)) 5
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 128)) 3
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 1024)) 2
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x6 .x28 0)) 1
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.BEQ .x6 .x0 offset)) 0
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) (offset : BitVec 13) :
    (state s offset).pc = if s.getMem 0x80400=0 then s.pc+44+signExtend13 offset else s.pc+48 := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_assoc]

theorem mem (s : MachineState) (offset : BitVec 13) (a : Word) :
    (state s offset).getMem a = if a=0x80438 then 0 else if a=0x80430 then 0 else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem stack (s : MachineState) (offset : BitVec 13) :
    (state s offset).getReg .x1=s.getReg .x1 ∧ (state s offset).getReg .x2=s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem keygen_code : Code keygen 0x11d4 1116 := by decide


end SigGolfCandidate.Hypertree.KeygenLeafEntry
