import SigGolfCandidate.Hypertree.ReusePrepare
namespace SigGolfCandidate.Hypertree.ConstantInitialPrepare
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false


def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  let s := execInstrBr s (.SD .x28 .x11 (-1072))
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  let s := execInstrBr s (.SD .x28 .x11 (-1064))
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  let s := execInstrBr s (.SD .x28 .x11 (-1056))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 48)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  let s := execInstrBr s (.ADDI .x13 .x0 1)
  let s := execInstrBr s (.SLLI .x13 .x13 32)
  execInstrBr s (.JAL .x0 112)

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x11 .x28 (216))) ∧
  instructionAt image (p + 4) = some (.base (.SD .x28 .x11 (-1048))) ∧
  instructionAt image (p + 8) = some (.base (.LD .x11 .x28 (224))) ∧
  instructionAt image (p + 12) = some (.base (.SD .x28 .x11 (-1040))) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x0 2)) ∧
  instructionAt image (p + 20) = some (.base (.LD .x11 .x28 (-56))) ∧
  instructionAt image (p + 24) = some (.base (.SLLI .x11 .x11 8)) ∧
  instructionAt image (p + 28) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 32) = some (.base (.LD .x11 .x28 (-16))) ∧
  instructionAt image (p + 36) = some (.base (.SLLI .x11 .x11 16)) ∧
  instructionAt image (p + 40) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 44) = some (.base (.LD .x11 .x28 (-8))) ∧
  instructionAt image (p + 48) = some (.base (.SLLI .x11 .x11 24)) ∧
  instructionAt image (p + 52) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 56) = some (.base (.LD .x11 .x28 (0))) ∧
  instructionAt image (p + 60) = some (.base (.SLLI .x11 .x11 32)) ∧
  instructionAt image (p + 64) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 68) = some (.base (.SD .x28 .x10 (-1080))) ∧
  instructionAt image (p + 72) = some (.base (.LD .x11 .x28 (-48))) ∧
  instructionAt image (p + 76) = some (.base (.SD .x28 .x11 (-1072))) ∧
  instructionAt image (p + 80) = some (.base (.LD .x11 .x28 (-40))) ∧
  instructionAt image (p + 84) = some (.base (.SD .x28 .x11 (-1064))) ∧
  instructionAt image (p + 88) = some (.base (.LD .x11 .x28 (-32))) ∧
  instructionAt image (p + 92) = some (.base (.SD .x28 .x11 (-1056))) ∧
  instructionAt image (p + 96) = some (.base (.ADDI .x28 .x28 (-1056))) ∧
  instructionAt image (p + 100) = some (.base (.ADDI .x10 .x28 (-24))) ∧
  instructionAt image (p + 104) = some (.base (.ADDI .x11 .x0 48)) ∧
  instructionAt image (p + 108) = some (.base (.ADDI .x12 .x28 744)) ∧
  instructionAt image (p + 112) = some (.base (.ADDI .x5 .x0 1)) ∧
  instructionAt image (p + 116) = some (.base (.ADDI .x13 .x0 1)) ∧
  instructionAt image (p + 120) = some (.base (.SLLI .x13 .x13 32)) ∧
  instructionAt image (p + 124) = some (.base (.JAL .x0 112))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 32 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31⟩ := code
  let s1 := execInstrBr s (.LD .x11 .x28 (216))
  let s2 := execInstrBr s1 (.SD .x28 .x11 (-1048))
  let s3 := execInstrBr s2 (.LD .x11 .x28 (224))
  let s4 := execInstrBr s3 (.SD .x28 .x11 (-1040))
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 2)
  let s6 := execInstrBr s5 (.LD .x11 .x28 (-56))
  let s7 := execInstrBr s6 (.SLLI .x11 .x11 8)
  let s8 := execInstrBr s7 (.ADD .x10 .x10 .x11)
  let s9 := execInstrBr s8 (.LD .x11 .x28 (-16))
  let s10 := execInstrBr s9 (.SLLI .x11 .x11 16)
  let s11 := execInstrBr s10 (.ADD .x10 .x10 .x11)
  let s12 := execInstrBr s11 (.LD .x11 .x28 (-8))
  let s13 := execInstrBr s12 (.SLLI .x11 .x11 24)
  let s14 := execInstrBr s13 (.ADD .x10 .x10 .x11)
  let s15 := execInstrBr s14 (.LD .x11 .x28 (0))
  let s16 := execInstrBr s15 (.SLLI .x11 .x11 32)
  let s17 := execInstrBr s16 (.ADD .x10 .x10 .x11)
  let s18 := execInstrBr s17 (.SD .x28 .x10 (-1080))
  let s19 := execInstrBr s18 (.LD .x11 .x28 (-48))
  let s20 := execInstrBr s19 (.SD .x28 .x11 (-1072))
  let s21 := execInstrBr s20 (.LD .x11 .x28 (-40))
  let s22 := execInstrBr s21 (.SD .x28 .x11 (-1064))
  let s23 := execInstrBr s22 (.LD .x11 .x28 (-32))
  let s24 := execInstrBr s23 (.SD .x28 .x11 (-1056))
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 (-1056))
  let s26 := execInstrBr s25 (.ADDI .x10 .x28 (-24))
  let s27 := execInstrBr s26 (.ADDI .x11 .x0 48)
  let s28 := execInstrBr s27 (.ADDI .x12 .x28 744)
  let s29 := execInstrBr s28 (.ADDI .x5 .x0 1)
  let s30 := execInstrBr s29 (.ADDI .x13 .x0 1)
  let s31 := execInstrBr s30 (.SLLI .x13 .x13 32)
  let s32 := execInstrBr s31 (.JAL .x0 112)
  change OrdinarySteps image s 32 s32
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x28 (216))) 31
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · have hb : s.getReg .x28 = 0x80438 := by
      simpa [execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s1, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x28 .x11 (-1048))) 30
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · have hb : s1.getReg .x28 = 0x80438 := by
      simpa [s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s2, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 (224))) 29
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · have hb : s2.getReg .x28 = 0x80438 := by
      simpa [s1, s2, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s3, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x11 (-1040))) 28
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · have hb : s3.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s4, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 2)) 27
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x11 .x28 (-56))) 26
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · have hb : s5.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s6, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x11 .x11 8)) 25
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x10 .x10 .x11)) 24
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 (-16))) 23
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · have hb : s8.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s9, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 16)) 22
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 21
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 (-8))) 20
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · have hb : s11.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s12, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s12 s13 _ (.base (.SLLI .x11 .x11 24)) 19
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADD .x10 .x10 .x11)) 18
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x11 .x28 (0))) 17
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · have hb : s14.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s15, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s15 s16 _ (.base (.SLLI .x11 .x11 32)) 16
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADD .x10 .x10 .x11)) 15
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.SD .x28 .x10 (-1080))) 14
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · have hb : s17.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s18, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s18 s19 _ (.base (.LD .x11 .x28 (-48))) 13
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · have hb : s18.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s19, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x11 (-1072))) 12
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · have hb : s19.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s20, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s20 s21 _ (.base (.LD .x11 .x28 (-40))) 11
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · have hb : s20.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s21, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s21 s22 _ (.base (.SD .x28 .x11 (-1064))) 10
  · have hp : s21.pc = p + 84 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c21
  · have hb : s21.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s22, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x11 .x28 (-32))) 9
  · have hp : s22.pc = p + 88 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c22
  · have hb : s22.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s23, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s23 s24 _ (.base (.SD .x28 .x11 (-1056))) 8
  · have hp : s23.pc = p + 92 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c23
  · have hb : s23.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s24, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x28 .x28 (-1056))) 7
  · have hp : s24.pc = p + 96 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x10 .x28 (-24))) 6
  · have hp : s25.pc = p + 100 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.ADDI .x11 .x0 48)) 5
  · have hp : s26.pc = p + 104 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x12 .x28 744)) 4
  · have hp : s27.pc = p + 108 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x5 .x0 1)) 3
  · have hp : s28.pc = p + 112 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x13 .x0 1)) 2
  · have hp : s29.pc = p + 116 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.SLLI .x13 .x13 32)) 1
  · have hp : s30.pc = p + 120 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.JAL .x0 112)) 0
  · have hp : s31.pc = p + 124 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c31
  · rfl
  exact OrdinarySteps.refl _

def beforeJump (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  let s := execInstrBr s (.SD .x28 .x11 (-1072))
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  let s := execInstrBr s (.SD .x28 .x11 (-1064))
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  let s := execInstrBr s (.SD .x28 .x11 (-1056))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 48)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  execInstrBr s (.ADDI .x5 .x0 1)

def tail (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x13 .x0 1)
  let s := execInstrBr s (.SLLI .x13 .x13 32)
  execInstrBr s (.JAL .x0 112)

theorem tail_equiv (s : MachineState) :
    tail s = (execInstrBr s (.JAL .x0 120)).setReg .x13 4294967296 := by
  cases s
  simp [tail, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    signExtend12, signExtend21, BitVec.add_assoc]
  funext r; cases r <;> rfl

theorem state_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    state s = (KeygenChainHeader.state (FusedPrepare.inputState s)).setReg .x13 4294967296 := by
  rw [← AddressReuseProof.header_equiv, ← FusedPrepare.state_equiv, ← ReuseChainBaseChunks.prepare_equiv s base]
  exact tail_equiv (beforeJump s)

/-- info: 'SigGolfCandidate.Hypertree.ConstantInitialPrepare.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
/-- info: 'SigGolfCandidate.Hypertree.ConstantInitialPrepare.tail_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tail_equiv
/-- info: 'SigGolfCandidate.Hypertree.ConstantInitialPrepare.state_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms state_equiv
end SigGolfCandidate.Hypertree.ConstantInitialPrepare
