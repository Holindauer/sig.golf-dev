import SigGolfCandidate.Hypertree.SignPrefixRandomizer
import SigGolfCandidate.Hypertree.PreludeResume

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
theorem messageCopyState_block (s : MachineState) (pc : s.pc = 0x104c) :
    OrdinarySteps signPrelude s 4 (messageCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s.pc = 0x104c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1050 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x40)) 1
  · have hp : s2.pc = 0x1054 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x1058 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem randomizerHeaderState_block (s : MachineState) (pc : s.pc = 0x1074) :
    OrdinarySteps signPrelude s 16 (randomizerHeaderState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 6)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x10 0)
  let s5 := execInstrBr s4 (.ADDI .x11 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 8)
  let s8 := execInstrBr s7 (.SD .x28 .x11 0)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x11 0)
  let s13 := execInstrBr s12 (.ADDI .x11 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 24)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 6)) 15
  · have hp : s.pc = 0x1074 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s1.pc = 0x1078 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 13
  · have hp : s2.pc = 0x107c := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s3.pc = 0x1080 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 11
  · have hp : s4.pc = 0x1084 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s5.pc = 0x1088 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 9
  · have hp : s6.pc = 0x108c := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 8
  · have hp : s7.pc = 0x1090 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 7
  · have hp : s8.pc = 0x1094 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s9.pc = 0x1098 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 5
  · have hp : s10.pc = 0x109c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 4
  · have hp : s11.pc = 0x10a0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 3
  · have hp : s12.pc = 0x10a4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x10a8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s14.pc = 0x10ac := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x10b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _


theorem randomizerHashState_block (s : MachineState) (pc : s.pc = 0x10b4) :
    OrdinarySteps signPrelude s 6 (randomizerHashState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 96)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s.pc = 0x10b4 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s1.pc = 0x10b8 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 96)) 3
  · have hp : s2.pc = 0x10bc := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s3.pc = 0x10c0 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s4.pc = 0x10c4 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s5.pc = 0x10c8 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem randomizerCopyState_block (s : MachineState) (pc : s.pc = 0x10d0) :
    OrdinarySteps signPrelude s 5 (randomizerCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x20)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x60)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · have hp : s.pc = 0x10d0 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x10d4 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x20)) 2
  · have hp : s2.pc = 0x10d8 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x60)) 1
  · have hp : s3.pc = 0x10dc := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x10e0 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem randomizer_copy_code : CopyCode signPrelude 0x10e4 := by decide

end SigGolfCandidate.Hypertree.Signing.Prelude
