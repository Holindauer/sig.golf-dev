import SigGolfCandidate.Hypertree.CounterCheck
import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.InplaceInitialPrepare
import SigGolfCandidate.Hypertree.CounterCore
import SigGolfCandidate.Hypertree.CounterArgs
import SigGolfCandidate.Hypertree.CheckReuse

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_short_check : CheckReuse.Code verify 0x14f4 := by unfold CheckReuse.Code; decide

theorem verify_cached_check : CounterCheck.Code verify 0x1580 := by unfold CounterCheck.Code; decide

theorem verify_restore_code : InplaceRestore.Code verify 0x1604 := by unfold InplaceRestore.Code; decide

end SigGolfCandidate.Hypertree.Verifying
