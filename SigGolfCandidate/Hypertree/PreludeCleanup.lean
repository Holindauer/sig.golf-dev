import SigGolfCandidate.Hypertree.PreludeRootCopy
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def cleanupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1024)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1032)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1040)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1048)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1280)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 1288)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 1)
  execInstrBr s (.JAL .x0 (-3380))

theorem cleanup_block (s : MachineState) (pc : s.pc = 0x1cd4) :
    OrdinarySteps signPrelude s 26 (cleanupState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 1024)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 1032)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.ADDI .x6 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 1040)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  let s13 := execInstrBr s12 (.ADDI .x6 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 1048)
  let s16 := execInstrBr s15 (.SD .x28 .x6 0)
  let s17 := execInstrBr s16 (.ADDI .x6 .x0 0)
  let s18 := execInstrBr s17 (.LUI .x28 0x80)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 1280)
  let s20 := execInstrBr s19 (.SD .x28 .x6 0)
  let s21 := execInstrBr s20 (.ADDI .x6 .x0 0)
  let s22 := execInstrBr s21 (.LUI .x28 0x80)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 1288)
  let s24 := execInstrBr s23 (.SD .x28 .x6 0)
  let s25 := execInstrBr s24 (.ADDI .x6 .x0 1)
  let s26 := execInstrBr s25 (.JAL .x0 (-3380))
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 25
  · have hp : s.pc = 0x1cd4 := by simp [execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 24
  · have hp : s1.pc = 0x1cd8 := by simp [s1, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 1024)) 23
  · have hp : s2.pc = 0x1cdc := by simp [s1, s2, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 22
  · have hp : s3.pc = 0x1ce0 := by simp [s1, s2, s3, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 21
  · have hp : s4.pc = 0x1ce4 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 20
  · have hp : s5.pc = 0x1ce8 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 1032)) 19
  · have hp : s6.pc = 0x1cec := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 18
  · have hp : s7.pc = 0x1cf0 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x6 .x0 0)) 17
  · have hp : s8.pc = 0x1cf4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 16
  · have hp : s9.pc = 0x1cf8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 1040)) 15
  · have hp : s10.pc = 0x1cfc := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 14
  · have hp : s11.pc = 0x1d00 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x6 .x0 0)) 13
  · have hp : s12.pc = 0x1d04 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s13.pc = 0x1d08 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 1048)) 11
  · have hp : s14.pc = 0x1d0c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x6 0)) 10
  · have hp : s15.pc = 0x1d10 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x6 .x0 0)) 9
  · have hp : s16.pc = 0x1d14 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s17.pc = 0x1d18 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 1280)) 7
  · have hp : s18.pc = 0x1d1c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x6 0)) 6
  · have hp : s19.pc = 0x1d20 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x6 .x0 0)) 5
  · have hp : s20.pc = 0x1d24 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x80)) 4
  · have hp : s21.pc = 0x1d28 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 1288)) 3
  · have hp : s22.pc = 0x1d2c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s23.pc = 0x1d30 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x6 .x0 1)) 1
  · have hp : s24.pc = 0x1d34 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.JAL .x0 (-3380))) 0
  · have hp : s25.pc = 0x1d38 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem cleanup_pc (s : MachineState) (pc : s.pc = 0x1cd4) :
    (cleanupState s).pc = 0x1004 := by
  simp [cleanupState, execInstrBr, pc, signExtend21]

theorem cleanup_ready (s : MachineState) : (cleanupState s).getReg .x6 = 1 := by
  simp [cleanupState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem cleanup_stack (s : MachineState) :
    (cleanupState s).getReg .x2 = s.getReg .x2 := by
  simp [cleanupState, execInstrBr, MachineState.getReg_setReg_ne]

theorem cleanup_mem (s : MachineState) (a : Word) :
    (cleanupState s).getMem a =
      if a = 0x80508 then 0 else if a = 0x80500 then 0 else
      if a = 0x80418 then 0 else if a = 0x80410 then 0 else
      if a = 0x80408 then 0 else if a = 0x80400 then 0 else s.getMem a := by
  simp [cleanupState, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem]

theorem cleanup_low (s : MachineState) (a : Word) (low : a.toNat < 0x80000) :
    (cleanupState s).getMem a = s.getMem a := by
  have ne (b : Word) (high : 0x80000 ≤ b.toNat) : a ≠ b := by
    intro eq; rw [eq] at low; omega
  rw [cleanup_mem]
  simp only [if_neg (ne 0x80508 (by decide)), if_neg (ne 0x80500 (by decide)), if_neg (ne 0x80418 (by decide)), if_neg (ne 0x80410 (by decide)), if_neg (ne 0x80408 (by decide)), if_neg (ne 0x80400 (by decide))]

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.cleanup_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cleanup_block
end SigGolfCandidate.Hypertree.Signing.Prelude
