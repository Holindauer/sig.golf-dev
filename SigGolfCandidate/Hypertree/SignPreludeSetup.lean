import SigGolfCandidate.Hypertree.SignEncodeSubroutine
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def deriveSetupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x440)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x80)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 159)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x1 (-2404))

def DeriveSetupCode (image : Image) : Prop :=
  instructionAt image 0x1c70 = some (.base (.ADDI .x6 .x0 1)) ∧
  instructionAt image 0x1c74 = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image 0x1c78 = some (.base (.ADDI .x28 .x28 0x440)) ∧
  instructionAt image 0x1c7c = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image 0x1c80 = some (.base (.LUI .x6 0x20)) ∧
  instructionAt image 0x1c84 = some (.base (.ADDI .x6 .x6 0x80)) ∧
  instructionAt image 0x1c88 = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image 0x1c8c = some (.base (.ADDI .x28 .x28 0x448)) ∧
  instructionAt image 0x1c90 = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image 0x1c94 = some (.base (.ADDI .x6 .x0 159)) ∧
  instructionAt image 0x1c98 = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image 0x1c9c = some (.base (.ADDI .x28 .x28 0x400)) ∧
  instructionAt image 0x1ca0 = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image 0x1ca4 = some (.base (.JAL .x1 (-2404)))

theorem deriveSetup_block (image : Image) (code : DeriveSetupCode image)
    (s : MachineState) (pc : s.pc = 0x1c70) :
    OrdinarySteps image s 14 (deriveSetupState s) := by
  rcases code with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  let s1 := execInstrBr s (.ADDI .x6 .x0 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x440)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x20)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 0x80)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x448)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 159)
  let s11 := execInstrBr s10 (.LUI .x28 0x80)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x400)
  let s13 := execInstrBr s12 (.SD .x28 .x6 0)
  let s14 := execInstrBr s13 (.JAL .x1 (-2404))
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 1)) 13
  · have hp : s.pc = 0x1c70 := by simp [execInstrBr, pc]
    rw [fetch_at, hp]; exact h0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s1.pc = 0x1c74 := by simp [s1, execInstrBr, pc]
    rw [fetch_at, hp]; exact h1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x440)) 11
  · have hp : s2.pc = 0x1c78 := by simp [s1, s2, execInstrBr, pc]
    rw [fetch_at, hp]; exact h2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 10
  · have hp : s3.pc = 0x1c7c := by simp [s1, s2, s3, execInstrBr, pc]
    rw [fetch_at, hp]; exact h3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x20)) 9
  · have hp : s4.pc = 0x1c80 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    rw [fetch_at, hp]; exact h4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 0x80)) 8
  · have hp : s5.pc = 0x1c84 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    rw [fetch_at, hp]; exact h5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 7
  · have hp : s6.pc = 0x1c88 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    rw [fetch_at, hp]; exact h6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x448)) 6
  · have hp : s7.pc = 0x1c8c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    rw [fetch_at, hp]; exact h7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 5
  · have hp : s8.pc = 0x1c90 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    rw [fetch_at, hp]; exact h8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x0 159)) 4
  · have hp : s9.pc = 0x1c94 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    rw [fetch_at, hp]; exact h9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x80)) 3
  · have hp : s10.pc = 0x1c98 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    rw [fetch_at, hp]; exact h10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x400)) 2
  · have hp : s11.pc = 0x1c9c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    rw [fetch_at, hp]; exact h11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s12.pc = 0x1ca0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    rw [fetch_at, hp]; exact h12
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.JAL .x1 (-2404))) 0
  · have hp : s13.pc = 0x1ca4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    rw [fetch_at, hp]; exact h13
  · rfl
  exact OrdinarySteps.refl _

theorem deriveSetup_pc (s : MachineState) (pc : s.pc = 0x1c70) :
    (deriveSetupState s).pc = 0x1340 := by
  simp [deriveSetupState, execInstrBr, pc, signExtend21]

theorem deriveSetup_return (s : MachineState) (pc : s.pc = 0x1c70) :
    (deriveSetupState s).getReg .x1 = 0x1ca8 := by
  simp [deriveSetupState, execInstrBr, pc, MachineState.getReg_setReg_eq]

theorem deriveSetup_stack (s : MachineState) :
    (deriveSetupState s).getReg .x2 = s.getReg .x2 := by
  simp [deriveSetupState, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Signing.deriveSetup_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms deriveSetup_block
end SigGolfCandidate.Hypertree.Signing
