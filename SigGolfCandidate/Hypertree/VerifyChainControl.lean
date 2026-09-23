import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastCopy16

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : ChainLoopControl.IncrementCode verify 0x161c (-332) := by decide

theorem verify_chain_code : FastCopy16.ChainCode verify 0x1500 := by
  unfold FastCopy16.ChainCode FastCopy16.InputCode FastCopy16.OutputCode
  decide

end SigGolfCandidate.Hypertree.Verifying
