import SigGolfCandidate.Hypertree.ChainLoopControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : ChainLoopControl.IncrementCode verify 0x161c (-332) := by decide

theorem verify_chain_code : KeygenChain.Code verify 0x1500 := by decide

end SigGolfCandidate.Hypertree.Verifying
