import SigGolfCandidate.Hypertree.FastCopy16
namespace SigGolfCandidate.Hypertree.Copy6
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def optimized (s : MachineState) (src dst : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.LD .x11 .x28 src)
  let s := execInstrBr s (.SD .x28 .x11 dst)
  let s := execInstrBr s (.LD .x11 .x28 (src+8))
  let s := execInstrBr s (.SD .x28 .x11 (dst+8))
  execInstrBr s (.JAL .x0 24)
def InputCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.LD .x11 .x28 1296)) ∧
  instructionAt image (p + 8) = some (.base (.SD .x28 .x11 32)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x11 .x28 1304)) ∧
  instructionAt image (p + 16) = some (.base (.SD .x28 .x11 40)) ∧
  instructionAt image (p + 20) = some (.base (.JAL .x0 24))
theorem chain_input_executes (image : Image) (p : Word) (code : InputCode image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 6 (optimized s 1296 32) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.LD .x11 .x28 1296)
  let s3 := execInstrBr s2 (.SD .x28 .x11 32)
  let s4 := execInstrBr s3 (.LD .x11 .x28 1304)
  let s5 := execInstrBr s4 (.SD .x28 .x11 40)
  let s6 := execInstrBr s5 (.JAL .x0 24)
  change OrdinarySteps image s 6 s6
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 5
  · have hp : s.pc = p + 0 := by simp [execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x11 .x28 1296)) 4
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x11 32)) 3
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 1304)) 2
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x11 40)) 1
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 24)) 0
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  exact OrdinarySteps.refl _
def OutputCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.LD .x11 .x28 768)) ∧
  instructionAt image (p + 8) = some (.base (.SD .x28 .x11 1296)) ∧
  instructionAt image (p + 12) = some (.base (.LD .x11 .x28 776)) ∧
  instructionAt image (p + 16) = some (.base (.SD .x28 .x11 1304)) ∧
  instructionAt image (p + 20) = some (.base (.JAL .x0 24))
theorem chain_output_executes (image : Image) (p : Word) (code : OutputCode image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 6 (optimized s 768 1296) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.LD .x11 .x28 768)
  let s3 := execInstrBr s2 (.SD .x28 .x11 1296)
  let s4 := execInstrBr s3 (.LD .x11 .x28 776)
  let s5 := execInstrBr s4 (.SD .x28 .x11 1304)
  let s6 := execInstrBr s5 (.JAL .x0 24)
  change OrdinarySteps image s 6 s6
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 5
  · have hp : s.pc = p + 0 := by simp [execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x11 .x28 768)) 4
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x11 1296)) 3
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 776)) 2
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x11 1304)) 1
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 24)) 0
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  exact OrdinarySteps.refl _
theorem input_spec (s : MachineState) :
    (optimized s 0x510 0x20).pc = s.pc + 44 ∧
    (optimized s 0x510 0x20).getReg .x1 = s.getReg .x1 ∧
    (optimized s 0x510 0x20).getReg .x2 = s.getReg .x2 ∧
    (∀ i : Fin 2, (optimized s 0x510 0x20).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem (Signing.wordAddress 0x80510 i.val)) ∧
    (∀ a, a ≠ 0x80020#64 → a ≠ 0x80028#64 → (optimized s 0x510 0x20).getMem a = s.getMem a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · intro i
    fin_cases i <;> simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, Signing.wordAddress]
  · intro a h0 h1
    simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, h0, h1]

theorem output_spec (s : MachineState) :
    (optimized s 0x300 0x510).pc = s.pc + 44 ∧
    (optimized s 0x300 0x510).getReg .x1 = s.getReg .x1 ∧
    (optimized s 0x300 0x510).getReg .x2 = s.getReg .x2 ∧
    (∀ i : Fin 2, (optimized s 0x300 0x510).getMem (Signing.wordAddress 0x80510 i.val) =
      s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
    (∀ a, a ≠ 0x80510#64 → a ≠ 0x80518#64 → (optimized s 0x300 0x510).getMem a = s.getMem a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · intro i
    fin_cases i <;> simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, Signing.wordAddress]
  · intro a h0 h1
    simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, h0, h1]

theorem copy_input (image : Image) (p : Word) (code : InputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 6 final ∧ final.pc = p+44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80020 i.val) = s.getMem (Signing.wordAddress 0x80510 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨hp, ra, sp, values, frame⟩ := input_spec s
  refine ⟨optimized s 0x510 0x20, chain_input_executes image p code s pc, by simpa [pc] using hp, values, ra, sp, ?_⟩
  intro a h
  apply frame a
  · simpa [Signing.wordAddress] using h 0
  · simpa [Signing.wordAddress] using h 1

theorem copy_output (image : Image) (p : Word) (code : OutputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 6 final ∧ final.pc = p+44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) = s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨hp, ra, sp, values, frame⟩ := output_spec s
  refine ⟨optimized s 0x300 0x510, chain_output_executes image p code s pc, by simpa [pc] using hp, values, ra, sp, ?_⟩
  intro a h
  apply frame a
  · simpa [Signing.wordAddress] using h 0
  · simpa [Signing.wordAddress] using h 1


/-- info: 'SigGolfCandidate.Hypertree.Copy6.copy_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_input
/-- info: 'SigGolfCandidate.Hypertree.Copy6.copy_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_output
end SigGolfCandidate.Hypertree.Copy6
