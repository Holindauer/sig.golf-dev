import SigGolfCandidate.Hypertree.KeygenNode

namespace SigGolfCandidate.Hypertree.KeygenNode

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def HeaderCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.ADDI .x10 .x0 4)) ∧
  instructionAt image (p + 4) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 8) = some (.base (.ADDI .x28 .x28 1024)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 16) = some (.base (.SLLI .x11 .x11 8)) ∧
  instructionAt image (p + 20) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 24) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 28) = some (.base (.ADDI .x28 .x28 0)) ∧
  instructionAt image (p + 32) = some (.base (.SD .x28 .x10 0)) ∧
  instructionAt image (p + 36) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 40) = some (.base (.ADDI .x28 .x28 1032)) ∧
  instructionAt image (p + 44) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 48) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 52) = some (.base (.ADDI .x28 .x28 8)) ∧
  instructionAt image (p + 56) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 60) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 64) = some (.base (.ADDI .x28 .x28 1040)) ∧
  instructionAt image (p + 68) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 72) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 76) = some (.base (.ADDI .x28 .x28 16)) ∧
  instructionAt image (p + 80) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 84) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 88) = some (.base (.ADDI .x28 .x28 1048)) ∧
  instructionAt image (p + 92) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 96) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 100) = some (.base (.ADDI .x28 .x28 24)) ∧
  instructionAt image (p + 104) = some (.base (.SD .x28 .x11 0)) ∧
  instructionAt image (p + 108) = some (.base (.LUI .x10 128)) ∧
  instructionAt image (p + 112) = some (.base (.ADDI .x10 .x10 0)) ∧
  instructionAt image (p + 116) = some (.base (.ADDI .x11 .x0 512)) ∧
  instructionAt image (p + 120) = some (.base (.LUI .x12 128)) ∧
  instructionAt image (p + 124) = some (.base (.ADDI .x12 .x12 768)) ∧
  instructionAt image (p + 128) = some (.base (.ADDI .x5 .x0 1))

instance (image : Image) (p : Word) : Decidable (HeaderCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 4)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1024)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
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

theorem header_block (image : Image) (p : Word) (code : HeaderCode image p)
    (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 33 (headerState s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32⟩ := code
  let s1 := execInstrBr s (.ADDI .x10 .x0 4)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 1024)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 128)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0)
  let s9 := execInstrBr s8 (.SD .x28 .x10 0)
  let s10 := execInstrBr s9 (.LUI .x28 128)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 1032)
  let s12 := execInstrBr s11 (.LD .x11 .x28 0)
  let s13 := execInstrBr s12 (.LUI .x28 128)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 8)
  let s15 := execInstrBr s14 (.SD .x28 .x11 0)
  let s16 := execInstrBr s15 (.LUI .x28 128)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 1040)
  let s18 := execInstrBr s17 (.LD .x11 .x28 0)
  let s19 := execInstrBr s18 (.LUI .x28 128)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 16)
  let s21 := execInstrBr s20 (.SD .x28 .x11 0)
  let s22 := execInstrBr s21 (.LUI .x28 128)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 1048)
  let s24 := execInstrBr s23 (.LD .x11 .x28 0)
  let s25 := execInstrBr s24 (.LUI .x28 128)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.SD .x28 .x11 0)
  let s28 := execInstrBr s27 (.LUI .x10 128)
  let s29 := execInstrBr s28 (.ADDI .x10 .x10 0)
  let s30 := execInstrBr s29 (.ADDI .x11 .x0 512)
  let s31 := execInstrBr s30 (.LUI .x12 128)
  let s32 := execInstrBr s31 (.ADDI .x12 .x12 768)
  let s33 := execInstrBr s32 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 4)) 32
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 31
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 1024)) 30
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 29
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 28
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 27
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 128)) 26
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 25
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 0)) 24
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 128)) 23
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 1032)) 22
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 21
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 128)) 20
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x11 0)) 18
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 128)) 17
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 1040)) 16
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 128)) 14
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 0)) 12
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 128)) 11
  · have hp : s21.pc = p + 84 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 1048)) 10
  · have hp : s22.pc = p + 88 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s23.pc = p + 92 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c23
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 128)) 8
  · have hp : s24.pc = p + 96 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s25.pc = p + 100 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s26.pc = p + 104 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c26
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x10 128)) 5
  · have hp : s27.pc = p + 108 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s28.pc = p + 112 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x11 .x0 512)) 3
  · have hp : s29.pc = p + 116 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x12 128)) 2
  · have hp : s30.pc = p + 120 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s31.pc = p + 124 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s32.pc = p + 128 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c32
  · rfl
  exact OrdinarySteps.refl _

theorem header_pc (s : MachineState) : (headerState s).pc = s.pc + 132 := by
  simp [headerState, execInstrBr, BitVec.add_assoc]

theorem header_regs (s : MachineState) :
    (headerState s).getReg .x5 = 1 ∧ (headerState s).getReg .x10 = 0x80000 ∧
    (headerState s).getReg .x11 = 512 ∧ (headerState s).getReg .x12 = 0x80300 := by
  simp [headerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem header_mem (s : MachineState) (a : Word) :
    (headerState s).getMem a =
      if a = 0x80018 then s.getMem 0x80418 else
      if a = 0x80010 then s.getMem 0x80410 else
      if a = 0x80008 then s.getMem 0x80408 else
      if a = 0x80000 then 4 + (s.getMem 0x80400 <<< 8) else s.getMem a := by
  simp [headerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem keygen_header_code : HeaderCode keygen 0x110c := by decide

theorem header_stack (s : MachineState) :
    (headerState s).getReg .x1 = s.getReg .x1 ∧
    (headerState s).getReg .x2 = s.getReg .x2 := by
  simp [headerState, execInstrBr, MachineState.getReg_setReg_ne]

theorem header_arithmetic (level : Nat) :
    (4 : Word) + (BitVec.ofNat 64 level <<< 8) = BitVec.ofNat 64 (4 + level * 2 ^ 8) := by
  change BitVec.ofNat 64 4 + (BitVec.ofNat 64 level <<< 8) = _
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 8 = BitVec.ofNat 64 (2 ^ 8) from by decide,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add]

/-- Header execution turns metadata and a copied child pair into the exact node query. -/
theorem header_words (s : MachineState) (level tree : Nat) (left right : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64 * i.val) 64)
    (hchildren : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x80020 i.val) =
      if i.val < 2 then left.extractLsb' (64 * i.val) 64
      else right.extractLsb' (64 * (i.val - 2)) 64) :
    ∀ i : Fin 8, (headerState s).getMem (Signing.wordAddress 0x80000 i.val) =
      inputWord level tree left right i := by
  have h0 := hindex 0
  have h1 := hindex 1
  have h2 := hindex 2
  have p0 := hchildren 0
  have p1 := hchildren 1
  have p2 := hchildren 2
  have p3 := hchildren 3
  norm_num [Signing.wordAddress] at h0 h1 h2 p0 p1 p2 p3
  intro i
  fin_cases i <;> simp only [Signing.wordAddress, inputWord, Fin.reduceFinMk,
    header_mem] <;> norm_num
  · change 4 + (s.getMem 0x80400 <<< 8) = _
    rw [hlevel]
    exact header_arithmetic level
  · exact h0
  · exact h1
  · exact h2
  · exact p0
  · exact p1
  · exact p2
  · exact p3

end SigGolfCandidate.Hypertree.KeygenNode
