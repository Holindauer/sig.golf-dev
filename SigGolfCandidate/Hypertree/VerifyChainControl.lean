import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.FastIncrement
import SigGolfCandidate.Hypertree.Copy6Chain

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : FastIncrement.Code verify 0x161c := by
  unfold FastIncrement.Code
  decide

theorem verify_chain_code : Copy6Chain.ChainCode verify 0x1500 := by
  unfold Copy6Chain.ChainCode Copy6.InputCode Copy6.OutputCode AddressReuseProof.headerCode
  decide

end SigGolfCandidate.Hypertree.Verifying
