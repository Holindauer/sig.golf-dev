import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.FusedChain

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : FastIncrement.Code verify 0x161c := by
  unfold FastIncrement.Code
  decide

theorem verify_chain_code : FusedChain.ChainCode verify 0x1500 := by
  unfold FusedChain.ChainCode FusedPrepare.Code Copy6.OutputCode
  decide

end SigGolfCandidate.Hypertree.Verifying
