import SigGolfCandidate.Hypertree.ReusePrepare
namespace SigGolfCandidate.Hypertree.CachedPrepare
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 216)
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 224)
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.LD .x10 .x28 (-1080))
  let s := execInstrBr s (.ADDI .x11 .x0 1)
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 48)

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x11 .x28 216)) ∧
  instructionAt image (p + 4) = some (.base (.SD .x28 .x11 (-1048))) ∧
  instructionAt image (p + 8) = some (.base (.LD .x11 .x28 224)) ∧
  instructionAt image (p + 12) = some (.base (.SD .x28 .x11 (-1040))) ∧
  instructionAt image (p + 16) = some (.base (.LD .x10 .x28 (-1080))) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x11 .x0 1)) ∧
  instructionAt image (p + 24) = some (.base (.SLLI .x11 .x11 32)) ∧
  instructionAt image (p + 28) = some (.base (.ADD .x10 .x10 .x11)) ∧
  instructionAt image (p + 32) = some (.base (.SD .x28 .x10 (-1080))) ∧
  instructionAt image (p + 36) = some (.base (.ADDI .x28 .x28 (-1056))) ∧
  instructionAt image (p + 40) = some (.base (.ADDI .x10 .x28 (-24))) ∧
  instructionAt image (p + 44) = some (.base (.ADDI .x11 .x0 384)) ∧
  instructionAt image (p + 48) = some (.base (.ADDI .x12 .x28 744)) ∧
  instructionAt image (p + 52) = some (.base (.ADDI .x5 .x0 1)) ∧
  instructionAt image (p + 56) = some (.base (.JAL .x0 48))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 15 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14⟩ := code
  let s1 := execInstrBr s (.LD .x11 .x28 216)
  let s2 := execInstrBr s1 (.SD .x28 .x11 (-1048))
  let s3 := execInstrBr s2 (.LD .x11 .x28 224)
  let s4 := execInstrBr s3 (.SD .x28 .x11 (-1040))
  let s5 := execInstrBr s4 (.LD .x10 .x28 (-1080))
  let s6 := execInstrBr s5 (.ADDI .x11 .x0 1)
  let s7 := execInstrBr s6 (.SLLI .x11 .x11 32)
  let s8 := execInstrBr s7 (.ADD .x10 .x10 .x11)
  let s9 := execInstrBr s8 (.SD .x28 .x10 (-1080))
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 (-1056))
  let s11 := execInstrBr s10 (.ADDI .x10 .x28 (-24))
  let s12 := execInstrBr s11 (.ADDI .x11 .x0 384)
  let s13 := execInstrBr s12 (.ADDI .x12 .x28 744)
  let s14 := execInstrBr s13 (.ADDI .x5 .x0 1)
  let s15 := execInstrBr s14 (.JAL .x0 48)
  change OrdinarySteps image s 15 s15
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x28 216)) 14
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · have hb : s.getReg .x28 = 0x80438 := by
      simpa [execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s1, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x28 .x11 (-1048))) 13
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · have hb : s1.getReg .x28 = 0x80438 := by
      simpa [s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s2, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 224)) 12
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · have hb : s2.getReg .x28 = 0x80438 := by
      simpa [s1, s2, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s3, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x11 (-1040))) 11
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · have hb : s3.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s4, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x10 .x28 (-1080))) 10
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · have hb : s4.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s5, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x11 .x0 1)) 9
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x11 .x11 32)) 8
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x10 .x10 .x11)) 7
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 (-1080))) 6
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · have hb : s8.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using base
    simp [s9, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 (-1056))) 5
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x10 .x28 (-24))) 4
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x11 .x0 384)) 3
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x12 .x28 744)) 2
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x5 .x0 1)) 1
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.JAL .x0 48)) 0
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · rfl
  exact OrdinarySteps.refl _

theorem mem (s : MachineState) (base : s.getReg .x28 = 0x80438) (a : Word) :
    (state s).getMem a =
      if a = 0x80000 then s.getMem 0x80000 + 4294967296 else
      if a = 0x80028 then s.getMem 0x80518 else
      if a = 0x80020 then s.getMem 0x80510 else s.getMem a := by
  simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, base, BitVec.add_assoc]

theorem regs (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (state s).getReg .x28 = 0x80018 ∧
    (state s).getReg .x10 = 0x80000 ∧
    (state s).getReg .x11 = 384 ∧
    (state s).getReg .x12 = 0x80300 ∧
    (state s).getReg .x5 = 1 := by
  simp [state, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12, signExtend21, base, BitVec.add_assoc]

theorem pc (s : MachineState) : (state s).pc = s.pc + 104 := by
  simp [state, execInstrBr, MachineState.setPC, signExtend21, BitVec.add_assoc]

/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem
/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms regs
/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pc
/-- The stored header describes the previous chain step. -/
def Ready (s : MachineState) : Prop :=
  s.getMem 0x80000 + 4294967296 =
    2 + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) +
      (s.getMem 0x80430 <<< 24) + (s.getMem 0x80438 <<< 32) ∧
  s.getMem 0x80008 = s.getMem 0x80408 ∧
  s.getMem 0x80010 = s.getMem 0x80410 ∧
  s.getMem 0x80018 = s.getMem 0x80418

theorem input_mem (s : MachineState) (a : Word) :
    (FusedPrepare.inputState s).getMem a =
      if a = 0x80028 then s.getMem 0x80518 else
      if a = 0x80020 then s.getMem 0x80510 else s.getMem a := by
  simp [FusedPrepare.inputState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem header_memory_equiv (s : MachineState)
    (base : s.getReg .x28 = 0x80438) (ready : Ready s) (a : Word) :
    (state s).getMem a =
      (KeygenChainHeader.state (FusedPrepare.inputState s)).getMem a := by
  obtain ⟨h0,h1,h2,h3⟩ := ready
  rw [mem s base a, KeygenChainHeader.mem]
  simp only [input_mem]
  by_cases a0 : a = 0x80000
  · subst a; simpa using h0
  by_cases a1 : a = 0x80008
  · subst a; simpa using h1
  by_cases a2 : a = 0x80010
  · subst a; simpa using h2
  by_cases a3 : a = 0x80018
  · subst a; simpa using h3
  simp only [a0,a1,a2,a3, if_false]

/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.header_memory_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms header_memory_equiv
theorem stack (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧ (state s).getReg .x2 = s.getReg .x2 := by
  simp [state, execInstrBr, MachineState.getReg_setReg_ne]

theorem frame (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (a : Word) (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80020) (h2 : a ≠ 0x80028) :
    (state s).getMem a = s.getMem a := by
  rw [mem s base a]
  simp only [h0,h1,h2,if_false]

/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stack
/-- info: 'SigGolfCandidate.Hypertree.CachedPrepare.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame
end SigGolfCandidate.Hypertree.CachedPrepare
