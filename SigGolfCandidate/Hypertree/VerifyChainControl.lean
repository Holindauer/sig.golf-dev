import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastHeaderChain

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : ChainLoopControl.IncrementCode verify 0x161c (-332) := by decide

theorem verify_chain_code : FastHeaderChain.ChainCode verify 0x1500 := by
  unfold FastHeaderChain.ChainCode FastCopy16.InputCode FastCopy16.OutputCode
  decide

end SigGolfCandidate.Hypertree.Verifying
