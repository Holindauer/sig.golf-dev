import SigGolfCandidate.Hypertree.InplaceInvariant
namespace SigGolfCandidate.Hypertree.PersistentHashArgs
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x10 .x28 (-1080))
  let s := execInstrBr s (.ADD .x10 .x10 .x13)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  execInstrBr s (.JAL .x0 76)

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x10 .x28 (-1080))) ∧
  instructionAt image (p + 4) = some (.base (.ADD .x10 .x10 .x13)) ∧
  instructionAt image (p + 8) = some (.base (.SD .x28 .x10 (-1080))) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x28 .x28 (-1056))) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x28 (-24))) ∧
  instructionAt image (p + 20) = some (.base (.JAL .x0 76))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 6 (state s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LD .x10 .x28 (-1080))
  let s2 := execInstrBr s1 (.ADD .x10 .x10 .x13)
  let s3 := execInstrBr s2 (.SD .x28 .x10 (-1080))
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 (-1056))
  let s5 := execInstrBr s4 (.ADDI .x10 .x28 (-24))
  let s6 := execInstrBr s5 (.JAL .x0 76)
  change OrdinarySteps image s 6 s6
  apply OrdinarySteps.step s s1 _ (.base (.LD .x10 .x28 (-1080))) 5
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · have hb : s.getReg .x28 = 0x80438 := by
      simp [execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s1, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x10 .x10 .x13)) 4
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x10 (-1080))) 3
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · have hb : s2.getReg .x28 = 0x80438 := by
      simp [s1, s2, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base]
    simp [s3, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 (-1056))) 2
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x28 (-24))) 1
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 76)) 0
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.Hypertree.PersistentHashArgs.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block

theorem equiv (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (bits : s.getReg .x11 = 48) (dst : s.getReg .x12 = 0x80020)
    (service : s.getReg .x5 = 1) : state s = InplacePrepare.state s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base bits dst service
    simp [state, InplacePrepare.state, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)
theorem check_preserves (s : MachineState) (r : Reg)
    (h6 : r ≠ .x6) (h7 : r ≠ .x7) :
    (InplaceCheck.shortCheck s).getReg r = s.getReg r := by
  simp [InplaceCheck.shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  split_ifs <;> simp_all

theorem finish_preserves (s : MachineState) (r : Reg)
    (h0 : r ≠ .x0) (h6 : r ≠ .x6) (h28 : r ≠ .x28) :
    (InplaceFinish.state s).getReg r = s.getReg r := by
  simp [InplaceFinish.state, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC, h0, h6, h28]

theorem hash_preserves (s : MachineState) (answer : BitVec 256) (r : Reg) :
    (writeHash s answer).getReg r = s.getReg r := hash_registers s answer r

/-- info: 'SigGolfCandidate.Hypertree.PersistentHashArgs.equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms equiv
/-- info: 'SigGolfCandidate.Hypertree.PersistentHashArgs.check_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_preserves
/-- info: 'SigGolfCandidate.Hypertree.PersistentHashArgs.finish_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_preserves
/-- info: 'SigGolfCandidate.Hypertree.PersistentHashArgs.hash_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hash_preserves
end SigGolfCandidate.Hypertree.PersistentHashArgs
