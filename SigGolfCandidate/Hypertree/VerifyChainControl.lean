import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.AddressReuseChain

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : ChainLoopControl.IncrementCode verify 0x161c (-332) := by decide

theorem verify_chain_code : AddressReuseChain.ChainCode verify 0x1500 := by
  unfold AddressReuseChain.ChainCode AddressReuseProof.inputCode AddressReuseProof.outputCode AddressReuseProof.headerCode
  decide

end SigGolfCandidate.Hypertree.Verifying
