import SigGolfCandidate.Hypertree.SignTreeStart
import SigGolfCandidate.Hypertree.PreludeTreeSettings
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem treeLeft_block (s : MachineState) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000) :
    OrdinarySteps signPrelude s 7 (treeLeftState s) := by
  have enter := enter_block signPrelude 0x13c8 sign_tree_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x13d0 := by rw [enter_pc, pc]; rfl
  have call := KeygenTreeControl.block signPrelude 0x13d0 0 364 sign_tree_left_code (enterState s) epc
  exact ordinary_trans signPrelude s _ _ 2 5 enter call


end SigGolfCandidate.Hypertree.Signing.Prelude
