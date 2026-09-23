import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.InitialConstantChain
import SigGolfCandidate.Hypertree.ConstantChain
import SigGolfCandidate.Hypertree.CheckReuse

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_short_check : CheckReuse.Code verify 0x14f4 := by unfold CheckReuse.Code; decide

theorem verify_chain_code : InitialConstantChain.ChainCode verify 0x1500 := by
  unfold InitialConstantChain.ChainCode ConstantInitialPrepare.Code ConstantFinish.Code
  decide

theorem verify_cached_check : ConstantCheck.Code verify 0x1580 := by unfold ConstantCheck.Code; decide

theorem verify_cached_code : ConstantChain.ChainCode verify 0x158c := by
  unfold ConstantChain.ChainCode ConstantPrepare.Code ConstantFinish.Code
  decide
end SigGolfCandidate.Hypertree.Verifying
