import SigGolfCandidate.Hypertree.InplaceInitialPrepare
import SigGolfCandidate.Hypertree.CheckReuse
import SigGolfCandidate.Hypertree.InplaceInvariant
namespace SigGolfCandidate.Hypertree.RegisterCounter
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def finish (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x28 .x28 1056)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-124))

theorem finish_equiv (s : MachineState) (base : s.getReg .x28 = 0x80018)
    (counter : s.getReg .x6 = s.getMem 0x80438) : finish s = InplaceFinish.state s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg, MachineState.getMem] at base counter
    simp [finish, InplaceFinish.state, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, counter, BitVec.add_assoc]

    all_goals first | rfl | (funext r; cases r <;> simp_all)

def check (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 7)
  execInstrBr s (.BEQ .x6 .x7 128)

def CheckCode (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADDI .x7 .x0 7)) ∧
  instructionAt image (p+4) = some (.base (.BEQ .x6 .x7 128))

theorem check_block (image : Image) (p : Word) (code : CheckCode image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 2 (check s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 7)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 7)) 1
  · simpa only [fetch_at, pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 (check s) _ (.base (.BEQ .x6 .x7 128)) 0
  · have hp : s1.pc = p+4 := by simp [s1, execInstrBr, pc]
    simpa only [fetch_at, hp] using code.2
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.check_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_block

theorem check_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) :
    check s = (InplaceCheck.shortCheck s).setPC
      (if s.getMem 0x80438 = 7 then s.pc+132 else s.pc+8) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg, MachineState.getMem] at base counter
    simp [check, InplaceCheck.shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend13, base, counter, BitVec.add_assoc]
    split_ifs <;> simp_all
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem prepare_counter (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) :
    (InplacePrepare.state s).getReg .x6 = (InplacePrepare.state s).getMem 0x80438 := by
  rw [InplacePrepare.mem s base, if_neg (by decide)]
  simpa [InplacePrepare.state, execInstrBr, MachineState.getReg_setReg_ne] using counter

theorem initial_counter (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) :
    (InplaceInitialPrepare.state s).getReg .x6 = (InplaceInitialPrepare.state s).getMem 0x80438 := by
  rw [InplaceInitialPrepare.state_equiv s base]
  simp only [MachineState.getMem_setReg]
  rw [KeygenChainHeader.frame _ _ (by intro i; fin_cases i <;> decide)]
  simpa [KeygenChainHeader.state, FusedPrepare.inputState, execInstrBr, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq, signExtend12] using counter

theorem finish_counter (s : MachineState) (base : s.getReg .x28 = 0x80018) :
    (finish s).getReg .x6 = (finish s).getMem 0x80438 := by
  simp [finish, execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    base, signExtend12]

theorem hash_counter (s : MachineState) (answer : BitVec 256)
    (destination : s.getReg .x12 = 0x80020) (counter : s.getReg .x6 = s.getMem 0x80438) :
    (writeHash s answer).getReg .x6 = (writeHash s answer).getMem 0x80438 := by
  rw [hash_registers, InplaceHash.frame s answer destination _ (by intro i; fin_cases i <;> decide)]
  exact counter

theorem initial_check_counter (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (CheckReuse.shortCheck s).getReg .x6 = (CheckReuse.shortCheck s).getMem 0x80438 := by
  simp [CheckReuse.shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, base]
  split_ifs <;> simp_all [MachineState.getReg]

/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.initial_check_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_check_counter

/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.hash_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_counter

/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.finish_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_equiv
/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.check_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_equiv
/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.prepare_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_counter
/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.initial_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_counter
/-- info: 'SigGolfCandidate.Hypertree.RegisterCounter.finish_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_counter
end SigGolfCandidate.Hypertree.RegisterCounter
