import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.InitialCachedChain
import SigGolfCandidate.Hypertree.CachedChain
import SigGolfCandidate.Hypertree.CheckReuse

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_short_check : CheckReuse.Code verify 0x14f4 := by unfold CheckReuse.Code; decide

theorem verify_chain_code : InitialCachedChain.ChainCode verify 0x1500 := by
  unfold InitialCachedChain.ChainCode ReusePrepare.Code CachedFinish.Code
  decide

theorem verify_cached_check : CachedCheck.Code verify 0x1578 := by unfold CachedCheck.Code; decide

theorem verify_cached_code : CachedChain.ChainCode verify 0x1584 := by
  unfold CachedChain.ChainCode CachedPrepare.Code CachedFinish.Code
  decide
end SigGolfCandidate.Hypertree.Verifying
