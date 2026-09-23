import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.InplaceInitialPrepare
import SigGolfCandidate.Hypertree.InplaceCore
import SigGolfCandidate.Hypertree.PersistentHashArgs
import SigGolfCandidate.Hypertree.CheckReuse

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_short_check : CheckReuse.Code verify 0x14f4 := by unfold CheckReuse.Code; decide

theorem verify_chain_code : InplaceInitialPrepare.Code verify 0x1500 ∧ InplaceCore.Code verify 0x15ec := by
  unfold InplaceInitialPrepare.Code InplaceCore.Code InplaceFinish.Code
  decide

theorem verify_cached_check : InplaceCheck.Code verify 0x1580 := by unfold InplaceCheck.Code; decide

theorem verify_cached_code : PersistentHashArgs.Code verify 0x158c ∧ InplaceCore.Code verify 0x15ec := by
  unfold PersistentHashArgs.Code InplaceCore.Code InplaceFinish.Code
  decide
theorem verify_restore_code : InplaceRestore.Code verify 0x1604 := by unfold InplaceRestore.Code; decide

end SigGolfCandidate.Hypertree.Verifying
