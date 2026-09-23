import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.KeygenSecretHeader

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.ADDI .x10 .x0 1)) ∧
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
  instructionAt image (p + 48) = some (.base (.ADDI .x28 .x28 1072)) ∧
  instructionAt image (p + 52) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 56) = some (.base (.SLLI .x11 .x11 24)) ∧
  instructionAt image (p + 60) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 64) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 68) = some (.base (.ADDI .x28 .x28 0)) ∧
  instructionAt image (p + 72) = some (.base (.SD .x28 .x10 0)) ∧
  instructionAt image (p + 76) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 80) = some (.base (.ADDI .x28 .x28 1032)) ∧
  instructionAt image (p + 84) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 88) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 92) = some (.base (.ADDI .x28 .x28 8)) ∧
  instructionAt image (p + 96) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 100) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 104) = some (.base (.ADDI .x28 .x28 1040)) ∧
  instructionAt image (p + 108) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 112) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 116) = some (.base (.ADDI .x28 .x28 16)) ∧
  instructionAt image (p + 120) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 124) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 128) = some (.base (.ADDI .x28 .x28 1048)) ∧
  instructionAt image (p + 132) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 136) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 140) = some (.base (.ADDI .x28 .x28 24)) ∧
  instructionAt image (p + 144) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 148) = some (.base (.LUI .x10 128)) ∧
  instructionAt image (p + 152) = some (.base (.ADDI .x10 .x10 0)) ∧
  instructionAt image (p + 156) = some (.base (.ADDI .x11 .x0 512)) ∧
  instructionAt image (p + 160) = some (.base (.LUI .x12 128)) ∧
  instructionAt image (p + 164) = some (.base (.ADDI .x12 .x12 768)) ∧
  instructionAt image (p + 168) = some (.base (.ADDI .x5 .x0 1))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 1)
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
  let s := execInstrBr s (.ADDI .x28 .x28 1072)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
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
  let s := execInstrBr s (.ADDI .x11 .x0 512)
  let s := execInstrBr s (.LUI .x12 128)
  let s := execInstrBr s (.ADDI .x12 .x12 768)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 43 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42⟩ := code
  let s1 := execInstrBr s (.ADDI .x10 .x0 1)
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
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 1072)
  let s14 := execInstrBr s13 (.LD .x11 .x28 0)
  let s15 := execInstrBr s14 (.SLLI .x11 .x11 24)
  let s16 := execInstrBr s15 (.ADD .x10 .x10 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 128)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 0)
  let s19 := execInstrBr s18 (.SD .x28 .x10 0)
  let s20 := execInstrBr s19 (.LUI .x28 128)
  let s21 := execInstrBr s20 (.ADDI .x28 .x28 1032)
  let s22 := execInstrBr s21 (.LD .x11 .x28 0)
  let s23 := execInstrBr s22 (.LUI .x28 128)
  let s24 := execInstrBr s23 (.ADDI .x28 .x28 8)
  let s25 := execInstrBr s24 (.SD .x28 .x11 0)
  let s26 := execInstrBr s25 (.LUI .x28 128)
  let s27 := execInstrBr s26 (.ADDI .x28 .x28 1040)
  let s28 := execInstrBr s27 (.LD .x11 .x28 0)
  let s29 := execInstrBr s28 (.LUI .x28 128)
  let s30 := execInstrBr s29 (.ADDI .x28 .x28 16)
  let s31 := execInstrBr s30 (.SD .x28 .x11 0)
  let s32 := execInstrBr s31 (.LUI .x28 128)
  let s33 := execInstrBr s32 (.ADDI .x28 .x28 1048)
  let s34 := execInstrBr s33 (.LD .x11 .x28 0)
  let s35 := execInstrBr s34 (.LUI .x28 128)
  let s36 := execInstrBr s35 (.ADDI .x28 .x28 24)
  let s37 := execInstrBr s36 (.SD .x28 .x11 0)
  let s38 := execInstrBr s37 (.LUI .x10 128)
  let s39 := execInstrBr s38 (.ADDI .x10 .x10 0)
  let s40 := execInstrBr s39 (.ADDI .x11 .x0 512)
  let s41 := execInstrBr s40 (.LUI .x12 128)
  let s42 := execInstrBr s41 (.ADDI .x12 .x12 768)
  let s43 := execInstrBr s42 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 1)) 42
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 41
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 1024)) 40
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 39
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 38
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 37
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 128)) 36
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 1064)) 35
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 34
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 16)) 33
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 32
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 128)) 31
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 1072)) 30
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LD .x11 .x28 0)) 29
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.SLLI .x11 .x11 24)) 28
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADD .x10 .x10 .x11)) 27
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 128)) 26
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 0)) 25
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x10 0)) 24
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.LUI .x28 128)) 23
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x28 .x28 1032)) 22
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.LD .x11 .x28 0)) 21
  · have hp : s21.pc = p + 84 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c21
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s22 s23 _ (.base (.LUI .x28 128)) 20
  · have hp : s22.pc = p + 88 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s23.pc = p + 92 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.SD .x28 .x11 0)) 18
  · have hp : s24.pc = p + 96 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c24
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s25 s26 _ (.base (.LUI .x28 128)) 17
  · have hp : s25.pc = p + 100 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.ADDI .x28 .x28 1040)) 16
  · have hp : s26.pc = p + 104 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s27.pc = p + 108 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c27
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s28 s29 _ (.base (.LUI .x28 128)) 14
  · have hp : s28.pc = p + 112 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s29.pc = p + 116 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.SD .x28 .x11 0)) 12
  · have hp : s30.pc = p + 120 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c30
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s31 s32 _ (.base (.LUI .x28 128)) 11
  · have hp : s31.pc = p + 124 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.ADDI .x28 .x28 1048)) 10
  · have hp : s32.pc = p + 128 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c32
  · rfl
  apply OrdinarySteps.step s33 s34 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s33.pc = p + 132 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c33
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s34 s35 _ (.base (.LUI .x28 128)) 8
  · have hp : s34.pc = p + 136 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c34
  · rfl
  apply OrdinarySteps.step s35 s36 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s35.pc = p + 140 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c35
  · rfl
  apply OrdinarySteps.step s36 s37 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s36.pc = p + 144 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c36
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s37 s38 _ (.base (.LUI .x10 128)) 5
  · have hp : s37.pc = p + 148 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c37
  · rfl
  apply OrdinarySteps.step s38 s39 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s38.pc = p + 152 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c38
  · rfl
  apply OrdinarySteps.step s39 s40 _ (.base (.ADDI .x11 .x0 512)) 3
  · have hp : s39.pc = p + 156 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c39
  · rfl
  apply OrdinarySteps.step s40 s41 _ (.base (.LUI .x12 128)) 2
  · have hp : s40.pc = p + 160 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c40
  · rfl
  apply OrdinarySteps.step s41 s42 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s41.pc = p + 164 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c41
  · rfl
  apply OrdinarySteps.step s42 s43 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s42.pc = p + 168 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c42
  · rfl
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) : (state s).pc = s.pc + 172 := by
  simp [state,execInstrBr,BitVec.add_assoc]

theorem regs (s : MachineState) :
    (state s).getReg .x5 = 1 ∧ (state s).getReg .x10 = 0x80000 ∧
    (state s).getReg .x11 = 512 ∧ (state s).getReg .x12 = 0x80300 := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem mem (s : MachineState) (a : Word) :
    (state s).getMem a =
      if a = 0x80018 then s.getMem 0x80418 else
      if a = 0x80010 then s.getMem 0x80410 else
      if a = 0x80008 then s.getMem 0x80408 else
      if a = 0x80000 then 1 + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) + (s.getMem 0x80430 <<< 24) else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem stack (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧ (state s).getReg .x2 = s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem keygen_code : Code keygen 0x122c := by decide

/-- The generated header exactly packs all domain-separation metadata. -/
theorem words (s : MachineState) (level tree leaf chain : Nat) (value : SecretKey)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 leaf)
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 8, (state s).getMem (Signing.wordAddress 0x80000 i.val) =
      KeygenDomain.secretInputWord (KeygenDomain.header 1 level leaf chain 0) tree value i := by
  rw [KeygenDomain.header_zero]
  apply KeygenDomain.secret_words_of_layout
  · rw [mem]
    change (BitVec.ofNat 64 1) + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) + (s.getMem 0x80430 <<< 24) = _
    rw [hlevel,hleaf,hchain]
    simp only [KeygenDomain.shift_ofNat,← BitVec.ofNat_add,KeygenDomain.header,Nat.zero_mul,Nat.add_zero]
  · intro i
    have h := hindex i
    fin_cases i <;> simp only [Signing.wordAddress,mem,Fin.reduceFinMk] <;> norm_num
    all_goals exact h
  · intro i
    have h := hvalue i
    fin_cases i <;> simp only [Signing.wordAddress,mem,Fin.reduceFinMk] <;> norm_num
    all_goals exact h

theorem frame (s : MachineState) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80000 i.val) :
    (state s).getMem a = s.getMem a := by
  have h0 : a ≠ (0x80000 : Word) := outside 0
  have h1 : a ≠ (0x80008 : Word) := outside 1
  have h2 : a ≠ (0x80010 : Word) := outside 2
  have h3 : a ≠ (0x80018 : Word) := outside 3
  rw [mem,if_neg h3,if_neg h2,if_neg h1,if_neg h0]

end SigGolfCandidate.Hypertree.KeygenSecretHeader
