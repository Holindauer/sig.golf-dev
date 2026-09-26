import SigGolfCandidate.Hypertree.SignSites
import SigGolfCandidate.Hypertree.PreludeChainCapture
import SigGolfCandidate.Hypertree.PreludeChainUnselected
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem sign_upper_secret_code : KeygenSecret.Code signPrelude 0x1584 := by decide
theorem sign_bottom_secret_code : KeygenSecret.Code signPrelude 0x19dc := by decide
theorem sign_endpoint_code : KeygenEndpoint.Code signPrelude 0x1874 (-832) := by decide
theorem sign_leaf_compress_code : KeygenLeaf.Code signPrelude 0x18c8 := by decide
theorem sign_leaf_enter_code : EnterCode signPrelude 0x154c := by decide
theorem sign_leaf_return_code : ReturnCode signPrelude 0x19d0 := by decide
theorem sign_bottom_return_code : ReturnCode signPrelude 0x1c64 := by decide
theorem sign_tree_enter_code : EnterCode signPrelude 0x13c8 := by decide
theorem sign_node_body_code : KeygenNode.BodyCode signPrelude 0x1460 := by decide
theorem sign_node_return_code : ReturnCode signPrelude 0x1540 := by decide


end SigGolfCandidate.Hypertree.Signing.Prelude
