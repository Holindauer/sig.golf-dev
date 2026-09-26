import SigGolfCandidate.Hypertree.PreludeLeafFinish
import SigGolfCandidate.Hypertree.SignLeafEntry
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
theorem sign_leaf_entry_code : KeygenLeafEntry.Code signPrelude 0x1554 1116 := by decide
theorem leafReady_block (s : MachineState) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0) :
    OrdinarySteps signPrelude s 14 (leafReady s) := by
  have entered := enter_block signPrelude 0x154c sign_leaf_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x1554 := by rw [enter_pc, pc]; rfl
  have entry := KeygenLeafEntry.block signPrelude 0x1554 1116 sign_leaf_entry_code (enterState s) epc
  exact ordinary_trans signPrelude _ _ _ 2 12 entered entry


end SigGolfCandidate.Hypertree.Signing.Prelude
