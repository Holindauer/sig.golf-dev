import SigGolfCandidate.Hypertree.ConstantInvariant
namespace SigGolfCandidate.Hypertree.InplacePrepare
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x10 .x28 (-1080))
  let s := execInstrBr s (.ADD .x10 .x10 .x13)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 48)
  let s := execInstrBr s (.ADDI .x12 .x28 8)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 64)

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x10 .x28 (-1080))) ∧
  instructionAt image (p + 4) = some (.base (.ADD .x10 .x10 .x13)) ∧
  instructionAt image (p + 8) = some (.base (.SD .x28 .x10 (-1080))) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x28 .x28 (-1056))) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x28 (-24))) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x11 .x0 48)) ∧
  instructionAt image (p + 24) = some (.base (.ADDI .x12 .x28 8)) ∧
  instructionAt image (p + 28) = some (.base (.ADDI .x5 .x0 1)) ∧
  instructionAt image (p + 32) = some (.base (.JAL .x0 64))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 9 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := code
  let s1 := execInstrBr s (.LD .x10 .x28 (-1080))
  let s2 := execInstrBr s1 (.ADD .x10 .x10 .x13)
  let s3 := execInstrBr s2 (.SD .x28 .x10 (-1080))
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 (-1056))
  let s5 := execInstrBr s4 (.ADDI .x10 .x28 (-24))
  let s6 := execInstrBr s5 (.ADDI .x11 .x0 48)
  let s7 := execInstrBr s6 (.ADDI .x12 .x28 8)
  let s8 := execInstrBr s7 (.ADDI .x5 .x0 1)
  let s9 := execInstrBr s8 (.JAL .x0 64)
  change OrdinarySteps image s 9 s9
  apply OrdinarySteps.step s s1 _ (.base (.LD .x10 .x28 (-1080))) 8
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · have hb : s.getReg .x28 = 0x80438 := by
      simp [execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s1, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x10 .x10 .x13)) 7
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x10 (-1080))) 6
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · have hb : s2.getReg .x28 = 0x80438 := by
      simp [s1, s2, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s3, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 (-1056))) 5
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x28 (-24))) 4
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x11 .x0 48)) 3
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x12 .x28 8)) 2
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x5 .x0 1)) 1
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.JAL .x0 64)) 0
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  exact OrdinarySteps.refl _

theorem mem (s : MachineState) (base : s.getReg .x28 = 0x80438) (a : Word) :
    (state s).getMem a = if a = 0x80000 then s.getMem 0x80000 + s.getReg .x13 else s.getMem a := by
  simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, base]

theorem pc (s : MachineState) : (state s).pc = s.pc + 96 := by
  simp [state, execInstrBr, signExtend21, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem preserved (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧
    (state s).getReg .x2 = s.getReg .x2 ∧
    (state s).getReg .x13 = s.getReg .x13 := by
  simp [state, execInstrBr, MachineState.getReg_setReg_ne]

theorem regs (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (state s).getReg .x28 = 0x80018 ∧ (state s).getReg .x10 = 0x80000 ∧
    (state s).getReg .x11 = 48 ∧ (state s).getReg .x12 = 0x80020 ∧
    (state s).getReg .x5 = 1 := by simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, base]
/-- info: 'SigGolfCandidate.Hypertree.InplacePrepare.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
/-- info: 'SigGolfCandidate.Hypertree.InplacePrepare.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem
/-- info: 'SigGolfCandidate.Hypertree.InplacePrepare.pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pc
/-- info: 'SigGolfCandidate.Hypertree.InplacePrepare.preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preserved

theorem header_memory_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (constant : s.getReg .x13 = 4294967296) (ready : CachedPrepare.Ready s) (a : Word) :
    (state s).getMem a = (KeygenChainHeader.state s).getMem a := by
  obtain ⟨h0,h1,h2,h3⟩ := ready
  rw [mem s base a, KeygenChainHeader.mem, constant]
  by_cases a0 : a = 0x80000
  · subst a; simpa using h0
  by_cases a1 : a = 0x80008
  · subst a; simpa using h1
  by_cases a2 : a = 0x80010
  · subst a; simpa using h2
  by_cases a3 : a = 0x80018
  · subst a; simpa using h3
  simp only [a0,a1,a2,a3,if_false]

/-- info: 'SigGolfCandidate.Hypertree.InplacePrepare.header_memory_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms header_memory_equiv
end SigGolfCandidate.Hypertree.InplacePrepare
