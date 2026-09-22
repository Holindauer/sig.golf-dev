import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.KeygenVerifyBottomLoad

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 1096)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x7 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x10 .x7 0)) ∧
  instructionAt image (p + 16) = some (.base (.LD .x11 .x7 8)) ∧
  instructionAt image (p + 20) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 24) = some (.base (.ADDI .x28 .x28 1296)) ∧
  instructionAt image (p + 28) = some (.base (.SD .x28 .x10 0)) ∧
  instructionAt image (p + 32) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 36) = some (.base (.ADDI .x28 .x28 1304)) ∧
  instructionAt image (p + 40) = some (.base (.SD .x28 .x11 0))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1096)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1296)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1304)
  execInstrBr s (.SD .x28 .x11 0)

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p)
    (safe : accessValid (s.getMem 0x80448) 8 = true) (safeNext : accessValid (s.getMem 0x80448+8) 8 = true) :
    OrdinarySteps image s 11 (state s) := by

  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 1096)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.LUI .x28 128)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 1296)
  let s8 := execInstrBr s7 (.SD .x28 .x10 0)
  let s9 := execInstrBr s8 (.LUI .x28 128)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 1304)
  let s11 := execInstrBr s10 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 10
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 1096)) 9
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 8
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 7
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safe
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 6
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safeNext
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 128)) 5
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 1296)) 4
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x10 0)) 3
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 128)) 2
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 1304)) 1
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) : (state s).pc=s.pc+44 := by
  simp [state,execInstrBr,BitVec.add_assoc]

theorem mem (s : MachineState) (a : Word) :
    (state s).getMem a=if a=0x80518 then s.getMem (s.getMem 0x80448+8) else
      if a=0x80510 then s.getMem (s.getMem 0x80448) else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem stack (s : MachineState) :
    (state s).getReg .x1=s.getReg .x1 ∧ (state s).getReg .x2=s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem code : Code verify 0x17a4 := by decide


end SigGolfCandidate.Hypertree.KeygenVerifyBottomLoad
