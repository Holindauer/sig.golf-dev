import SigGolfCandidate.Hypertree.ChainLoopControl
namespace SigGolfCandidate.Hypertree.FastIncrement
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1080)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-324))
theorem state_equiv (s : MachineState) : state s = ChainLoopControl.increment s (-332) := by
  cases s
  simp [state, ChainLoopControl.increment, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, BitVec.add_assoc]
  funext r
  cases r <;> rfl
def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 1080)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image (p + 16) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 20) = some (.base (.JAL .x0 (-324)))
theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 6 (ChainLoopControl.increment s (-332)) := by
  rw [← state_equiv]
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 1080)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.SD .x28 .x6 0)
  let s6 := execInstrBr s5 (.JAL .x0 (-324))
  change OrdinarySteps image s 6 s6
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 5
  · have hp : s.pc = p + 0 := by simp [execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 1080)) 4
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 3
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 2
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 (-324))) 0
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  exact OrdinarySteps.refl _
/-- info: 'SigGolfCandidate.Hypertree.FastIncrement.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
end SigGolfCandidate.Hypertree.FastIncrement
