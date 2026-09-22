import SigGolfCandidate.Hypertree.VerifyChainLoop

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def chainSource (s : MachineState) : Word := s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)

def chainValueState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x430)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SLLI .x10 .x6 4)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x510)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x518)
  execInstrBr s (.SD .x28 .x11 0)

theorem chainValueState_block (s : MachineState) (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSource s) 8 = true) (valid8 : accessValid (chainSource s + 8) 8 = true) :
    OrdinarySteps verify s 16 (chainValueState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x430)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x448)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.SLLI .x10 .x6 4)
  let s8 := execInstrBr s7 (.ADD .x7 .x7 .x10)
  let s9 := execInstrBr s8 (.LD .x10 .x7 0)
  let s10 := execInstrBr s9 (.LD .x11 .x7 8)
  let s11 := execInstrBr s10 (.LUI .x28 0x80)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x510)
  let s13 := execInstrBr s12 (.SD .x28 .x10 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 0x518)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 15
  · have hp : s.pc = 0x1490 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x430)) 14
  · have hp : s1.pc = 0x1494 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 13
  · have hp : s2.pc = 0x1498 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s3.pc = 0x149c := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x448)) 11
  · have hp : s4.pc = 0x14a0 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 10
  · have hp : s5.pc = 0x14a4 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x10 .x6 4)) 9
  · have hp : s6.pc = 0x14a8 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x7 .x7 .x10)) 8
  · have hp : s7.pc = 0x14ac := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x10 .x7 0)) 7
  · have hp : s8.pc = 0x14b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chainSource] using valid0
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x11 .x7 8)) 6
  · have hp : s9.pc = 0x14b4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chainSource] using valid8
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x80)) 5
  · have hp : s10.pc = 0x14b8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x510)) 4
  · have hp : s11.pc = 0x14bc := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x10 0)) 3
  · have hp : s12.pc = 0x14c0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x14c4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 0x518)) 1
  · have hp : s14.pc = 0x14c8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x14cc := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

def chainDigitState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x600)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LBU .x10 .x7 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  execInstrBr s (.SD .x28 .x10 0)

theorem chainDigitState_block (s : MachineState) (pc : s.pc = 0x14d0)
    (valid : accessValid (0x80600 + s.getReg .x6) 1 = true) :
    OrdinarySteps verify s 7 (chainDigitState s) := by
  let s1 := execInstrBr s (.LUI .x7 0x80)
  let s2 := execInstrBr s1 (.ADDI .x7 .x7 0x600)
  let s3 := execInstrBr s2 (.ADD .x7 .x7 .x6)
  let s4 := execInstrBr s3 (.LBU .x10 .x7 0)
  let s5 := execInstrBr s4 (.LUI .x28 0x80)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x438)
  let s7 := execInstrBr s6 (.SD .x28 .x10 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x7 0x80)) 6
  · have hp : s.pc = 0x14d0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x7 .x7 0x600)) 5
  · have hp : s1.pc = 0x14d4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x7 .x7 .x6)) 4
  · have hp : s2.pc = 0x14d8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LBU .x10 .x7 0)) 3
  · have hp : s3.pc = 0x14dc := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using valid
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s4.pc = 0x14e0 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x438)) 1
  · have hp : s5.pc = 0x14e4 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x10 0)) 0
  · have hp : s6.pc = 0x14e8 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem chainValueState_mem (s : MachineState) (a : Word) :
    (chainValueState s).getMem a = if a = 0x80518 then s.getMem (chainSource s + 8) else
      if a = 0x80510 then s.getMem (chainSource s) else s.getMem a := by
  simp [chainValueState, chainSource, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_chain (s : MachineState) :
    (chainValueState s).getReg .x6 = s.getMem 0x80430 := by
  simp [chainValueState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_pc (s : MachineState) : (chainValueState s).pc = s.pc + 64 := by
  simp [chainValueState, execInstrBr, BitVec.add_assoc]

theorem chainValueState_stack (s : MachineState) :
    (chainValueState s).getReg .x1 = s.getReg .x1 ∧ (chainValueState s).getReg .x2 = s.getReg .x2 := by
  simp [chainValueState, execInstrBr, MachineState.getReg_setReg_ne]

theorem chainDigitState_mem (s : MachineState) (a : Word) :
    (chainDigitState s).getMem a = if a = 0x80438 then
      (s.getByte (0x80600 + s.getReg .x6)).zeroExtend 64 else s.getMem a := by
  simp [chainDigitState, execInstrBr, signExtend12, Expansion.mem_setMem, MachineState.getByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainDigitState_pc (s : MachineState) : (chainDigitState s).pc = s.pc + 28 := by
  simp [chainDigitState, execInstrBr, BitVec.add_assoc]

theorem chainDigitState_stack (s : MachineState) :
    (chainDigitState s).getReg .x1 = s.getReg .x1 ∧ (chainDigitState s).getReg .x2 = s.getReg .x2 := by
  simp [chainDigitState, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chainValueState_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainValueState_block

end SigGolfCandidate.Hypertree.Verifying
