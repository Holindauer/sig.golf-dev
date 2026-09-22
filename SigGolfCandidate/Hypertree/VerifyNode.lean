import SigGolfCandidate.Hypertree.KeygenNodeExecution

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv Keygen
set_option maxRecDepth 4096

/-- The verifier uses the same certified parent-node computation as key generation. -/
theorem node_body_code : KeygenNode.BodyCode verify 0x136c := by decide

theorem node_return_code : ReturnCode verify 0x144c := by decide

theorem tree_enter_code : EnterCode verify 0x12f0 := by decide

theorem leaf_enter_code : EnterCode verify 0x1458 := by decide

theorem leaf_return_code : ReturnCode verify 0x1798 := by decide

theorem bottom_return_code : ReturnCode verify 0x18fc := by decide

/-- info: 'SigGolfCandidate.Hypertree.Verifying.node_body_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms node_body_code

end SigGolfCandidate.Hypertree.Verifying
