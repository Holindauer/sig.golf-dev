import SigGolfCandidate.Hypertree.SignChainCapture
import SigGolfCandidate.Hypertree.SignChainUnselected
import SigGolfCandidate.Hypertree.KeygenSecretExecution
import SigGolfCandidate.Hypertree.KeygenLeafExecution
import SigGolfCandidate.Hypertree.KeygenNodeExecution
import SigGolfCandidate.Hypertree.KeygenEndpoint

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv Keygen
set_option maxRecDepth 4096

theorem sign_upper_secret_code : KeygenSecret.Code sign 0x1584 := by decide
theorem sign_bottom_secret_code : KeygenSecret.Code sign 0x19dc := by decide
theorem sign_endpoint_code : KeygenEndpoint.Code sign 0x1874 (-832) := by decide
theorem sign_leaf_compress_code : KeygenLeaf.Code sign 0x18c8 := by decide
theorem sign_leaf_enter_code : EnterCode sign 0x154c := by decide
theorem sign_leaf_return_code : ReturnCode sign 0x19d0 := by decide
theorem sign_bottom_return_code : ReturnCode sign 0x1c64 := by decide
theorem sign_tree_enter_code : EnterCode sign 0x13c8 := by decide
theorem sign_node_body_code : KeygenNode.BodyCode sign 0x1460 := by decide
theorem sign_node_return_code : ReturnCode sign 0x1540 := by decide

end SigGolfCandidate.Hypertree.Signing
