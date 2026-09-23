import SigGolfCandidate.Hypertree.InplaceInitialPrepare
import SigGolfCandidate.Hypertree.CheckReuse
import SigGolfCandidate.Hypertree.InplaceInvariant
namespace SigGolfCandidate.Hypertree.PersistentLimit
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def check (s : MachineState) : MachineState := execInstrBr s (.BEQ .x6 .x7 132)

theorem check_block (image : Image) (p : Word)
    (code : instructionAt image p = some (.base (.BEQ .x6 .x7 132)))
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 1 (check s) := by
  apply OrdinarySteps.step s (check s) _ (.base (.BEQ .x6 .x7 132)) 0
  · simpa only [fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _

theorem check_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) (limit : s.getReg .x7 = 7) :
    check s = (InplaceCheck.shortCheck s).setPC
      (if s.getMem 0x80438 = 7 then s.pc+132 else s.pc+4) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg,MachineState.getMem] at base counter limit
    simp [check,InplaceCheck.shortCheck,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC,signExtend12,signExtend13,base,counter,limit,BitVec.add_assoc]
    split_ifs <;> simp_all
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem initial_installs (s : MachineState) : (CheckReuse.shortCheck s).getReg .x7 = 7 := by
  simp [CheckReuse.shortCheck,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
  split_ifs <;> rfl

theorem prepare_preserves (s : MachineState) : (InplacePrepare.state s).getReg .x7 = s.getReg .x7 := by
  simp [InplacePrepare.state,execInstrBr,MachineState.getReg_setReg_ne]

theorem initial_preserves (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (InplaceInitialPrepare.state s).getReg .x7 = s.getReg .x7 := by
  rw [InplaceInitialPrepare.state_equiv s base]
  simp [KeygenChainHeader.state,FusedPrepare.inputState,execInstrBr,MachineState.getReg_setReg_ne]

theorem finish_preserves (s : MachineState) : (InplaceFinish.state s).getReg .x7 = s.getReg .x7 := by
  simp [InplaceFinish.state,execInstrBr,MachineState.getReg_setReg_ne]

theorem hash_preserves (s : MachineState) (answer : BitVec 256) :
    (writeHash s answer).getReg .x7 = s.getReg .x7 := hash_registers s answer .x7

theorem check_preserves (s : MachineState) (r : Reg) : (check s).getReg r = s.getReg r := by
  simp [check,execInstrBr,MachineState.getReg,MachineState.setPC]
  split_ifs <;> rfl

/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.check_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_preserves

/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.check_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_block
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.check_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_equiv
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.initial_installs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_installs
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.prepare_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_preserves
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.initial_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_preserves
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.finish_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_preserves
/-- info: 'SigGolfCandidate.Hypertree.PersistentLimit.hash_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hash_preserves
end SigGolfCandidate.Hypertree.PersistentLimit
