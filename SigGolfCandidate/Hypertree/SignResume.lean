import SigGolfCandidate.Hypertree.SignPrepare
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def initializeTailState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x440)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x80)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem initializeTail_block (image : Image)
    (code : ∀ p : Word, 0x1004 ≤ p.toNat → p.toNat ≤ 0x1030 →
      instructionAt image p = instructionAt sign p)
    (s : MachineState) (pc : s.pc = 0x1004) :
    OrdinarySteps image s 12 (initializeTailState s) := by
  let s1 := s
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x440)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x20)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 0x80)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x448)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 0x20)
  let s11 := execInstrBr s10 (.LUI .x7 0x80)
  let s12 := execInstrBr s11 (.ADDI .x7 .x7 0x20)
  let s13 := execInstrBr s12 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 11
  · have hp : s1.pc = 0x1004 := by simp [s1, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x440)) 10
  · have hp : s2.pc = 0x1008 := by simp [s1, s2, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s3.pc = 0x100c := by simp [s1, s2, s3, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x20)) 8
  · have hp : s4.pc = 0x1010 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 0x80)) 7
  · have hp : s5.pc = 0x1014 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s6.pc = 0x1018 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x448)) 5
  · have hp : s7.pc = 0x101c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s8.pc = 0x1020 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x0 0x20)) 3
  · have hp : s9.pc = 0x1024 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s10.pc = 0x1028 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s11.pc = 0x102c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s12.pc = 0x1030 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    rw [fetch_at, hp, code _ (by decide) (by decide)]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem initializeTail_after_first (s : MachineState) :
    initializeTailState (execInstrBr s (.ADDI .x6 .x0 1)) = initializeState s := by rfl

/-- Restoring the displaced ADDI permits reuse of the original initialization state. -/
theorem restored_entry (s : MachineState) (ready : s.getReg .x6 = 1) :
    execInstrBr (s.setPC (s.pc - 4)) (.ADDI .x6 .x0 1) = s := by
  cases s
  simp only [execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg,
    BitVec.zero_add, BitVec.sub_add_cancel]
  congr 1
  funext r
  cases r <;> simp_all [MachineState.getReg, signExtend12]

theorem initializeTail_equiv (s : MachineState) (ready : s.getReg .x6 = 1) :
    initializeTailState s = initializeState (s.setPC (s.pc - 4)) := by
  rw [← initializeTail_after_first, restored_entry s ready]

/-- info: 'SigGolfCandidate.Hypertree.Signing.initializeTail_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initializeTail_block
/-- info: 'SigGolfCandidate.Hypertree.Signing.initializeTail_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initializeTail_equiv
end SigGolfCandidate.Hypertree.Signing
