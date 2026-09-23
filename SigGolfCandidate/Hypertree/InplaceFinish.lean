import SigGolfCandidate.Hypertree.ConstantInvariant
namespace SigGolfCandidate.Hypertree.InplaceFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x28 .x28 1056)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-128))

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.ADDI .x28 .x28 1056)) ∧
  instructionAt image (p + 4) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 8) = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image (p + 12) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 16) = some (.base (.JAL .x0 (-128)))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80018) :
    OrdinarySteps image s 5 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4⟩ := code
  let s1 := execInstrBr s (.ADDI .x28 .x28 1056)
  let s2 := execInstrBr s1 (.LD .x6 .x28 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x6 1)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.JAL .x0 (-128))
  change OrdinarySteps image s 5 s5
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x28 .x28 1056)) 4
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x6 .x28 0)) 3
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · have hb : s1.getReg .x28 = 0x80438 := by
      simp [s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s2, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x6 1)) 2
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · have hb : s3.getReg .x28 = 0x80438 := by
      simp [s1, s2, s3, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s4, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.JAL .x0 (-128))) 0
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem mem (s : MachineState) (base : s.getReg .x28 = 0x80018) (a : Word) :
    (state s).getMem a = if a = 0x80438 then s.getMem 0x80438 + 1 else s.getMem a := by
  simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, base]

theorem pc (s : MachineState) : (state s).pc = s.pc - 112 := by
  simp [state, execInstrBr, signExtend21, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem preserved (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧
    (state s).getReg .x2 = s.getReg .x2 ∧
    (state s).getReg .x13 = s.getReg .x13 := by
  simp [state, execInstrBr, MachineState.getReg_setReg_ne]

theorem base (s : MachineState) (h : s.getReg .x28 = 0x80018) : (state s).getReg .x28 = 0x80438 := by
  simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, h]
/-- info: 'SigGolfCandidate.Hypertree.InplaceFinish.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
/-- info: 'SigGolfCandidate.Hypertree.InplaceFinish.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem
/-- info: 'SigGolfCandidate.Hypertree.InplaceFinish.pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pc
/-- info: 'SigGolfCandidate.Hypertree.InplaceFinish.preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preserved
end SigGolfCandidate.Hypertree.InplaceFinish
