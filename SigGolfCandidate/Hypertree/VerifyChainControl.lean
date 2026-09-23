import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.FinishChain

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_code : FinishChain.ChainCode verify 0x1500 := by
  unfold FinishChain.ChainCode FusedPrepare.Code FusedFinish.Code
  decide

end SigGolfCandidate.Hypertree.Verifying
