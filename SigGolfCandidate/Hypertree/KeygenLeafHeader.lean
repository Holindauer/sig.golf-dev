import SigGolfCandidate.Hypertree.KeygenLeafQuery

namespace SigGolfCandidate.Hypertree.KeygenLeafHeader

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.ADDI .x10 .x0 3)) ∧
  instructionAt image (p + 4) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 8) = some (.base (.ADDI .x28 .x28 1024)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 16) = some (.base (.SLLI .x11 .x11 8)) ∧
  instructionAt image (p + 20) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 24) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 28) = some (.base (.ADDI .x28 .x28 1064)) ∧
  instructionAt image (p + 32) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 36) = some (.base (.SLLI .x11 .x11 16)) ∧
  instructionAt image (p + 40) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 44) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 48) = some (.base (.ADDI .x28 .x28 0)) ∧
  instructionAt image (p + 52) = some (.base (.SD .x28 .x10 0)) ∧
  instructionAt image (p + 56) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 60) = some (.base (.ADDI .x28 .x28 1032)) ∧
  instructionAt image (p + 64) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 68) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 72) = some (.base (.ADDI .x28 .x28 8)) ∧
  instructionAt image (p + 76) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 80) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 84) = some (.base (.ADDI .x28 .x28 1040)) ∧
  instructionAt image (p + 88) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 92) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 96) = some (.base (.ADDI .x28 .x28 16)) ∧
  instructionAt image (p + 100) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 104) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 108) = some (.base (.ADDI .x28 .x28 1048)) ∧
  instructionAt image (p + 112) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 116) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 120) = some (.base (.ADDI .x28 .x28 24)) ∧
  instructionAt image (p + 124) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 128) = some (.base (.LUI .x10 128)) ∧
  instructionAt image (p + 132) = some (.base (.ADDI .x10 .x10 0)) ∧
  instructionAt image (p + 136) = some (.base (.LUI .x11 2)) ∧
  instructionAt image (p + 140) = some (.base (.ADDI .x11 .x11 2048)) ∧
  instructionAt image (p + 144) = some (.base (.LUI .x12 128)) ∧
  instructionAt image (p + 148) = some (.base (.ADDI .x12 .x12 768)) ∧
  instructionAt image (p + 152) = some (.base (.ADDI .x5 .x0 1))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 3)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1024)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1064)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1032)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1040)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1048)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 128)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.LUI .x11 2)
  let s := execInstrBr s (.ADDI .x11 .x11 2048)
  let s := execInstrBr s (.LUI .x12 128)
  let s := execInstrBr s (.ADDI .x12 .x12 768)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 39 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38⟩ := code
  let s1 := execInstrBr s (.ADDI .x10 .x0 3)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 1024)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 128)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 1064)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.SLLI .x11 .x11 16)
  let s11 := execInstrBr s10 (.ADD .x10 .x10 .x11)
  let s12 := execInstrBr s11 (.LUI .x28 128)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0)
  let s14 := execInstrBr s13 (.SD .x28 .x10 0)
  let s15 := execInstrBr s14 (.LUI .x28 128)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 1032)
  let s17 := execInstrBr s16 (.LD .x11 .x28 0)
  let s18 := execInstrBr s17 (.LUI .x28 128)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 8)
  let s20 := execInstrBr s19 (.SD .x28 .x11 0)
  let s21 := execInstrBr s20 (.LUI .x28 128)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 1040)
  let s23 := execInstrBr s22 (.LD .x11 .x28 0)
  let s24 := execInstrBr s23 (.LUI .x28 128)
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 16)
  let s26 := execInstrBr s25 (.SD .x28 .x11 0)
  let s27 := execInstrBr s26 (.LUI .x28 128)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 1048)
  let s29 := execInstrBr s28 (.LD .x11 .x28 0)
  let s30 := execInstrBr s29 (.LUI .x28 128)
  let s31 := execInstrBr s30 (.ADDI .x28 .x28 24)
  let s32 := execInstrBr s31 (.SD .x28 .x11 0)
  let s33 := execInstrBr s32 (.LUI .x10 128)
  let s34 := execInstrBr s33 (.ADDI .x10 .x10 0)
  let s35 := execInstrBr s34 (.LUI .x11 2)
  let s36 := execInstrBr s35 (.ADDI .x11 .x11 2048)
  let s37 := execInstrBr s36 (.LUI .x12 128)
  let s38 := execInstrBr s37 (.ADDI .x12 .x12 768)
  let s39 := execInstrBr s38 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 3)) 38
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 37
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 1024)) 36
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 35
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 34
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 33
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 128)) 32
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 1064)) 31
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 30
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 16)) 29
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 28
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 128)) 27
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0)) 26
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x10 0)) 25
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 128)) 24
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 1032)) 23
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LD .x11 .x28 0)) 22
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 128)) 21
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 8)) 20
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x11 0)) 19
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 128)) 18
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 1040)) 17
  · have hp : s21.pc = p + 84 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x11 .x28 0)) 16
  · have hp : s22.pc = p + 88 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c22
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s23 s24 _ (.base (.LUI .x28 128)) 15
  · have hp : s23.pc = p + 92 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x28 .x28 16)) 14
  · have hp : s24.pc = p + 96 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.SD .x28 .x11 0)) 13
  · have hp : s25.pc = p + 100 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c25
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 128)) 12
  · have hp : s26.pc = p + 104 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 1048)) 11
  · have hp : s27.pc = p + 108 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s28.pc = p + 112 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c28
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x28 128)) 9
  · have hp : s29.pc = p + 116 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x28 .x28 24)) 8
  · have hp : s30.pc = p + 120 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.SD .x28 .x11 0)) 7
  · have hp : s31.pc = p + 124 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c31
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s32 s33 _ (.base (.LUI .x10 128)) 6
  · have hp : s32.pc = p + 128 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c32
  · rfl
  apply OrdinarySteps.step s33 s34 _ (.base (.ADDI .x10 .x10 0)) 5
  · have hp : s33.pc = p + 132 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c33
  · rfl
  apply OrdinarySteps.step s34 s35 _ (.base (.LUI .x11 2)) 4
  · have hp : s34.pc = p + 136 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c34
  · rfl
  apply OrdinarySteps.step s35 s36 _ (.base (.ADDI .x11 .x11 2048)) 3
  · have hp : s35.pc = p + 140 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c35
  · rfl
  apply OrdinarySteps.step s36 s37 _ (.base (.LUI .x12 128)) 2
  · have hp : s36.pc = p + 144 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c36
  · rfl
  apply OrdinarySteps.step s37 s38 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s37.pc = p + 148 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c37
  · rfl
  apply OrdinarySteps.step s38 s39 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s38.pc = p + 152 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c38
  · rfl
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) : (state s).pc = s.pc + 156 := by
  simp [state,execInstrBr,BitVec.add_assoc]

theorem regs (s : MachineState) :
    (state s).getReg .x5 = 1 ∧ (state s).getReg .x10 = 0x80000 ∧
    (state s).getReg .x11 = 6144 ∧ (state s).getReg .x12 = 0x80300 := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem mem (s : MachineState) (a : Word) :
    (state s).getMem a =
      if a = 0x80018 then s.getMem 0x80418 else
      if a = 0x80010 then s.getMem 0x80410 else
      if a = 0x80008 then s.getMem 0x80408 else
      if a = 0x80000 then 3 + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem stack (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧ (state s).getReg .x2 = s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem keygen_code : Code keygen 0x1574 := by decide

theorem frame (s : MachineState) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80000 i.val) :
    (state s).getMem a = s.getMem a := by
  have h0 : a ≠ (0x80000:Word) := outside 0
  have h1 : a ≠ (0x80008:Word) := outside 1
  have h2 : a ≠ (0x80010:Word) := outside 2
  have h3 : a ≠ (0x80018:Word) := outside 3
  rw [mem,if_neg h3,if_neg h2,if_neg h1,if_neg h0]

def endpointWord (values : Reference.Chain → Reference.Digest) (i : Fin 92) : Word :=
  (values ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb' (64*(i.val%2)) 64

theorem words (s : MachineState) (level tree leaf : Nat) (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 leaf)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80020 i.val) = endpointWord values i) :
    ∀ i : Fin 96, (state s).getMem (Signing.wordAddress 0x80000 i.val) =
      KeygenLeaf.inputWord (BitVec.ofNat 64 (3+level*2^8+leaf*2^16)) tree values i := by
  have head : 3 + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) =
      BitVec.ofNat 64 (3+level*2^8+leaf*2^16) := by
    rw [hlevel,hleaf]
    change BitVec.ofNat 64 3 + _ + _ = _
    simp only [KeygenDomain.shift_ofNat,← BitVec.ofNat_add]
  have h0 := hindex 0
  have h1 := hindex 1
  have h2 := hindex 2
  norm_num [Signing.wordAddress] at h0 h1 h2
  intro i
  by_cases first : i.val<4
  · obtain ⟨i,hi⟩ := i
    dsimp at first
    interval_cases i <;> simp only [Signing.wordAddress,KeygenLeaf.inputWord,Fin.reduceFinMk,mem] <;> norm_num
    · exact head
    · exact h0
    · exact h1
    · exact h2
  · have outside : ∀ j : Fin 4, Signing.wordAddress 0x80000 i.val ≠ Signing.wordAddress 0x80000 j.val := by
      intro j
      exact Signing.wordAddress_injective 0x80000 96 (by decide) i.val j.val i.isLt (by have := j.isLt; omega) (by have := j.isLt; omega)
    rw [frame s _ outside]
    have index : i.val/1-4 < 92 := by have := i.isLt; omega
    have addr : Signing.wordAddress 0x80000 i.val = Signing.wordAddress 0x80020 (i.val-4) := by
      unfold Signing.wordAddress
      congr 1
      omega
    rw [addr,hvalues ⟨i.val-4,by omega⟩]
    simp only [KeygenLeaf.inputWord,show i.val≠0 from by omega,first,↓reduceIte,endpointWord]

end SigGolfCandidate.Hypertree.KeygenLeafHeader
