import SigGolfCandidate.Hypertree.AddressReuseProof
namespace SigGolfCandidate.Hypertree.FusedPrepare
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
def inputState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.LD .x11 .x28 1296)
  let s := execInstrBr s (.SD .x28 .x11 32)
  let s := execInstrBr s (.LD .x11 .x28 1304)
  let s := execInstrBr s (.SD .x28 .x11 40)
  execInstrBr s (.JAL .x0 24)
def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.LD .x11 .x28 1296)
  let s := execInstrBr s (.SD .x28 .x11 32)
  let s := execInstrBr s (.LD .x11 .x28 1304)
  let s := execInstrBr s (.SD .x28 .x11 40)
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 1024)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 1064)
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 1072)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 1080)
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LD .x11 .x28 1032)
  let s := execInstrBr s (.SD .x28 .x11 8)
  let s := execInstrBr s (.LD .x11 .x28 1040)
  let s := execInstrBr s (.SD .x28 .x11 16)
  let s := execInstrBr s (.LD .x11 .x28 1048)
  let s := execInstrBr s (.SD .x28 .x11 24)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 116)
theorem state_equiv (s : MachineState) : state s = AddressReuseProof.header (inputState s) := by
  cases s
  simp [state, inputState, AddressReuseProof.header, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, BitVec.add_assoc]
  funext r
  cases r <;> rfl
def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.LD .x11 .x28 1296)) ∧
  instructionAt image (p + 8) = some (.base (.SD .x28 .x11 32)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x11 .x28 1304)) ∧
  instructionAt image (p + 16) = some (.base (.SD .x28 .x11 40)) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x10 .x0 2)) ∧
  instructionAt image (p + 24) = some (.base (.LD .x11 .x28 1024)) ∧
  instructionAt image (p + 28) = some (.base (.SLLI .x11 .x11 8)) ∧
  instructionAt image (p + 32) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 36) = some (.base (.LD .x11 .x28 1064)) ∧
  instructionAt image (p + 40) = some (.base (.SLLI .x11 .x11 16)) ∧
  instructionAt image (p + 44) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 48) = some (.base (.LD .x11 .x28 1072)) ∧
  instructionAt image (p + 52) = some (.base (.SLLI .x11 .x11 24)) ∧
  instructionAt image (p + 56) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 60) = some (.base (.LD .x11 .x28 1080)) ∧
  instructionAt image (p + 64) = some (.base (.SLLI .x11 .x11 32)) ∧
  instructionAt image (p + 68) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 72) = some (.base (.SD .x28 .x10 0)) ∧
  instructionAt image (p + 76) = some (.base (.LD .x11 .x28 1032)) ∧
  instructionAt image (p + 80) = some (.base (.SD .x28 .x11 8)) ∧
  instructionAt image (p + 84) = some (.base (.LD .x11 .x28 1040)) ∧
  instructionAt image (p + 88) = some (.base (.SD .x28 .x11 16)) ∧
  instructionAt image (p + 92) = some (.base (.LD .x11 .x28 1048)) ∧
  instructionAt image (p + 96) = some (.base (.SD .x28 .x11 24)) ∧
  instructionAt image (p + 100) = some (.base (.ADDI .x28 .x28 24)) ∧
  instructionAt image (p + 104) = some (.base (.ADDI .x10 .x28 (-24))) ∧
  instructionAt image (p + 108) = some (.base (.ADDI .x11 .x0 384)) ∧
  instructionAt image (p + 112) = some (.base (.ADDI .x12 .x28 744)) ∧
  instructionAt image (p + 116) = some (.base (.ADDI .x5 .x0 1)) ∧
  instructionAt image (p + 120) = some (.base (.JAL .x0 116))
theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 31 (KeygenChainHeader.state (inputState s)) := by
  rw [← AddressReuseProof.header_equiv, ← state_equiv]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.LD .x11 .x28 1296)
  let s3 := execInstrBr s2 (.SD .x28 .x11 32)
  let s4 := execInstrBr s3 (.LD .x11 .x28 1304)
  let s5 := execInstrBr s4 (.SD .x28 .x11 40)
  let s6 := execInstrBr s5 (.ADDI .x10 .x0 2)
  let s7 := execInstrBr s6 (.LD .x11 .x28 1024)
  let s8 := execInstrBr s7 (.SLLI .x11 .x11 8)
  let s9 := execInstrBr s8 (.ADD .x10 .x10 .x11)
  let s10 := execInstrBr s9 (.LD .x11 .x28 1064)
  let s11 := execInstrBr s10 (.SLLI .x11 .x11 16)
  let s12 := execInstrBr s11 (.ADD .x10 .x10 .x11)
  let s13 := execInstrBr s12 (.LD .x11 .x28 1072)
  let s14 := execInstrBr s13 (.SLLI .x11 .x11 24)
  let s15 := execInstrBr s14 (.ADD .x10 .x10 .x11)
  let s16 := execInstrBr s15 (.LD .x11 .x28 1080)
  let s17 := execInstrBr s16 (.SLLI .x11 .x11 32)
  let s18 := execInstrBr s17 (.ADD .x10 .x10 .x11)
  let s19 := execInstrBr s18 (.SD .x28 .x10 0)
  let s20 := execInstrBr s19 (.LD .x11 .x28 1032)
  let s21 := execInstrBr s20 (.SD .x28 .x11 8)
  let s22 := execInstrBr s21 (.LD .x11 .x28 1040)
  let s23 := execInstrBr s22 (.SD .x28 .x11 16)
  let s24 := execInstrBr s23 (.LD .x11 .x28 1048)
  let s25 := execInstrBr s24 (.SD .x28 .x11 24)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.ADDI .x10 .x28 (-24))
  let s28 := execInstrBr s27 (.ADDI .x11 .x0 384)
  let s29 := execInstrBr s28 (.ADDI .x12 .x28 744)
  let s30 := execInstrBr s29 (.ADDI .x5 .x0 1)
  let s31 := execInstrBr s30 (.JAL .x0 116)
  change OrdinarySteps image s 31 s31
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 30
  · have hp : s.pc = p + 0 := by simp [execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x11 .x28 1296)) 29
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x11 32)) 28
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 1304)) 27
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x11 40)) 26
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x0 2)) 25
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x11 .x28 1024)) 24
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.SLLI .x11 .x11 8)) 23
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADD .x10 .x10 .x11)) 22
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x11 .x28 1064)) 21
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.SLLI .x11 .x11 16)) 20
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADD .x10 .x10 .x11)) 19
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x11 .x28 1072)) 18
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SLLI .x11 .x11 24)) 17
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADD .x10 .x10 .x11)) 16
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.LD .x11 .x28 1080)) 15
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.SLLI .x11 .x11 32)) 14
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADD .x10 .x10 .x11)) 13
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.LD .x11 .x28 1032)) 11
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 8)) 10
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LD .x11 .x28 1040)) 9
  · have hp : s21.pc = p + 84 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c21
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s22 s23 _ (.base (.SD .x28 .x11 16)) 8
  · have hp : s22.pc = p + 88 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c22
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 1048)) 7
  · have hp : s23.pc = p + 92 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c23
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.SD .x28 .x11 24)) 6
  · have hp : s24.pc = p + 96 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c24
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 5
  · have hp : s25.pc = p + 100 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.ADDI .x10 .x28 (-24))) 4
  · have hp : s26.pc = p + 104 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x11 .x0 384)) 3
  · have hp : s27.pc = p + 108 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x12 .x28 744)) 2
  · have hp : s28.pc = p + 112 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x5 .x0 1)) 1
  · have hp : s29.pc = p + 116 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.JAL .x0 116)) 0
  · have hp : s30.pc = p + 120 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c30
  · rfl
  exact OrdinarySteps.refl _
/-- info: 'SigGolfCandidate.Hypertree.FusedPrepare.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
end SigGolfCandidate.Hypertree.FusedPrepare
