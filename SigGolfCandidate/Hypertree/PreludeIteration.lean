import SigGolfCandidate.Hypertree.SignIteration
import SigGolfCandidate.Hypertree.PreludeSecretPrepare
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem sign_selected_iteration (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (message : Reference.Digest)
    (pc : s.pc = 0x1584) (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (settings : CaptureSettings s pointer chain (Reference.digit message chain)) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 8 8 final ∧
      instructions ≤ 1071 ∧ cycles ≤ 1127 ∧
      final.pc = (if chain.val + 1 = 46 then 0x18c8 else 0x1584) ∧
      LeafData final secretKey level tree side (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64) ∧
      CapturedValue final pointer chain ((Reference.signLayer hash secretKey level tree side message).values chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideIteration chain a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨computed, steps, cycles, pre, stepsBound, cyclesBound, computedPC, computedData, captured,
    computedRA, computedSP, computedFrame⟩ :=
    sign_selected_chain hash s secretKey pointer level tree side chain message pc upper valid data settings
  obtain ⟨final, post, finalPC, counter, endpoint, finalRA, finalSP, finalFrame⟩ :=
    KeygenEndpoint.store_endpoint signPrelude 0x1874 (-832) sign_endpoint_code computed chain
      (Reference.endpoint hash secretKey level tree side chain) computedPC computedData.chainEq computedData.valueEq
  have frame (a : Word) (outside : OutsideIteration chain a)
      (captureOutside : ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) : final.getMem a = s.getMem a := by
    rw [finalFrame a outside.2.1 outside.2.2, computedFrame a outside.1 captureOutside]
  refine ⟨final, steps + 21, cycles + 21, pre.trans post.trace, by omega, by omega, ?_,
    data.iteration s final secretKey pointer level tree side chain valid counter frame, endpoint, ?_,
    finalRA.trans computedRA, finalSP.trans computedSP, frame⟩
  · simpa [signExtend13] using finalPC
  · intro i
    have outside := signature_outside_endpoint pointer chain valid i
    rw [finalFrame _ outside.1 outside.2]
    exact captured i

/-- The unselected leaf's corresponding iteration never changes the signature buffer. -/
theorem sign_unselected_iteration (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 8 8 final ∧
      instructions ≤ 1071 ∧ cycles ≤ 1127 ∧
      final.pc = (if chain.val + 1 = 46 then 0x18c8 else 0x1584) ∧
      LeafData final secretKey level tree side (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideIteration chain a → final.getMem a = s.getMem a) := by
  obtain ⟨computed, steps, cycles, pre, stepsBound, cyclesBound, computedPC, computedData,
    computedRA, computedSP, computedFrame⟩ :=
    sign_unselected_chain hash s secretKey pointer level tree side chain pc valid ptr data unselected
  obtain ⟨final, post, finalPC, counter, endpoint, finalRA, finalSP, finalFrame⟩ :=
    KeygenEndpoint.store_endpoint signPrelude 0x1874 (-832) sign_endpoint_code computed chain
      (Reference.endpoint hash secretKey level tree side chain) computedPC computedData.chainEq computedData.valueEq
  have frame (a : Word) (outside : OutsideIteration chain a) : final.getMem a = s.getMem a := by
    rw [finalFrame a outside.2.1 outside.2.2, computedFrame a outside.1]
  refine ⟨final, steps + 21, cycles + 21, pre.trans post.trace, by omega, by omega, ?_,
    data.iteration s final secretKey pointer level tree side chain valid counter (fun a outside _ => frame a outside),
    endpoint, finalRA.trans computedRA, finalSP.trans computedSP, frame⟩
  simpa [signExtend13] using finalPC


end SigGolfCandidate.Hypertree.Signing.Prelude
