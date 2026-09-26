import SigGolfCandidate.Hypertree.PreludePrepared
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

def entryJump (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 3184)

theorem entryJump_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps signPrelude s 1 (entryJump s) := by
  apply OrdinarySteps.step s (entryJump s) _ (.base (.JAL .x0 3184)) 0
  · rw [fetch_at, pc]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem entryJump_pc (s : MachineState) (pc : s.pc = 0x1000) :
    (entryJump s).pc = 0x1c70 := by simp [entryJump, execInstrBr, signExtend21, pc]

theorem entryJump_mem (s : MachineState) (a : Word) :
    (entryJump s).getMem a = s.getMem a := by simp [entryJump, execInstrBr]

theorem entryJump_stack (s : MachineState) :
    (entryJump s).getReg .x2 = s.getReg .x2 := by
  simp [entryJump, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.entryJump_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entryJump_block
end SigGolfCandidate.Hypertree.Signing.Prelude
