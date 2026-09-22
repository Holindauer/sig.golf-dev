import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.VerifyChainRecovery

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing

/-- The shared endpoint-store theorem instantiated for the verifier’s chain loop. -/
theorem store_endpoint (s : MachineState) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x163c) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps verify s 21 final ∧
      final.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) = value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 → (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) → final.getMem a = s.getMem a) := by
  exact KeygenEndpoint.store_endpoint verify 0x163c (-508) verify_endpoint_code s chain value pc counter valueWords

end SigGolfCandidate.Hypertree.Verifying
