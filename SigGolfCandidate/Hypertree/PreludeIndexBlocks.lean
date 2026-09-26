import SigGolfCandidate.Hypertree.PreludePrefixRandomizer

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
theorem pkCopyState_block (s : MachineState) (pc : s.pc = 0x10fc) :
    OrdinarySteps signPrelude s 4 (pkCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0x40)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x20)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 2)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0x40)) 3
  · have hp : s.pc = 0x10fc := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1100 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s2.pc = 0x1104 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s3.pc = 0x1108 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem indexMessageCopyState_block (s : MachineState) (pc : s.pc = 0x1124) :
    OrdinarySteps signPrelude s 4 (indexMessageCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x30)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s.pc = 0x1124 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1128 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x30)) 1
  · have hp : s2.pc = 0x112c := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x1130 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem inputRandomizerCopyState_block (s : MachineState) (pc : s.pc = 0x114c) :
    OrdinarySteps signPrelude s 5 (inputRandomizerCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x20)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x60)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x50)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x20)) 4
  · have hp : s.pc = 0x114c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x60)) 3
  · have hp : s1.pc = 0x1150 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1154 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x50)) 1
  · have hp : s3.pc = 0x1158 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x115c := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem indexHeaderState_block (s : MachineState) (pc : s.pc = 0x1178) :
    OrdinarySteps signPrelude s 16 (indexHeaderState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 5)
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
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 5)) 15
  · have hp : s.pc = 0x1178 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s1.pc = 0x117c := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 13
  · have hp : s2.pc = 0x1180 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s3.pc = 0x1184 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 11
  · have hp : s4.pc = 0x1188 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s5.pc = 0x118c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 9
  · have hp : s6.pc = 0x1190 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 8
  · have hp : s7.pc = 0x1194 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 7
  · have hp : s8.pc = 0x1198 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s9.pc = 0x119c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 5
  · have hp : s10.pc = 0x11a0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 4
  · have hp : s11.pc = 0x11a4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 3
  · have hp : s12.pc = 0x11a8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x11ac := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s14.pc = 0x11b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x11b4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _


theorem indexHashState_block (s : MachineState) (pc : s.pc = 0x11b8) :
    OrdinarySteps signPrelude s 6 (indexHashState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 112)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s.pc = 0x11b8 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s1.pc = 0x11bc := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 112)) 3
  · have hp : s2.pc = 0x11c0 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s3.pc = 0x11c4 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s4.pc = 0x11c8 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s5.pc = 0x11cc := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem indexCopyState_block (s : MachineState) (pc : s.pc = 0x11d4) :
    OrdinarySteps signPrelude s 5 (indexCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x408)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 2)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · have hp : s.pc = 0x11d4 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x11d8 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x11dc := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x408)) 1
  · have hp : s3.pc = 0x11e0 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x11e4 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem indexStoreState_block (s : MachineState) (pc : s.pc = 0x1200) :
    OrdinarySteps signPrelude s 8 (indexStoreState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x310)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 32)
  let s5 := execInstrBr s4 (.SRLI .x6 .x6 32)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x418)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 7
  · have hp : s.pc = 0x1200 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x310)) 6
  · have hp : s1.pc = 0x1204 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x1208 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 32)) 4
  · have hp : s3.pc = 0x120c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x6 .x6 32)) 3
  · have hp : s4.pc = 0x1210 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s5.pc = 0x1214 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x418)) 1
  · have hp : s6.pc = 0x1218 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s7.pc = 0x121c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

end SigGolfCandidate.Hypertree.Signing.Prelude
