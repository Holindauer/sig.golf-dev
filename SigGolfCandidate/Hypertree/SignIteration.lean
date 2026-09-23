import SigGolfCandidate.Hypertree.SignSecretPrepare
import SigGolfCandidate.Hypertree.EndpointStore

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def OutsideIteration (chain : Reference.Chain) (a : Word) : Prop :=
  OutsideChainWork a ∧ a ≠ 0x80430 ∧
  ∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val

theorem outsideIteration_metadata (chain : Reference.Chain) (a : Word)
    (low : a.toNat < 0x80800) (work : OutsideChainWork a) (counter : a ≠ 0x80430) :
    OutsideIteration chain a := by
  refine ⟨work, counter, ?_⟩
  intro i eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ib := i.isLt
  simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
  omega

theorem signature_outside_endpoint (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer) (i : Fin 2) :
    wordAddress (pointer + 16 * chain.val) i.val ≠ 0x80430 ∧
      ∀ j : Fin 2, wordAddress (pointer + 16 * chain.val) i.val ≠ KeygenEndpoint.endpointAddress chain.val j.val := by
  have cb := chain.isLt
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    simp [wordAddress] at h
    omega
  · intro j eq
    have h := congrArg BitVec.toNat eq
    have jb := j.isLt
    simp only [wordAddress, KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
    omega

/-- Metadata and secret key survive an iteration, except for the intended chain counter increment. -/
theorem LeafData.iteration (s final : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (counter : final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1))
    (frame : ∀ a, OutsideIteration chain a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :
    LeafData final secretKey level tree side (chain.val+1) := by
  have keep (a : Word) (outside : OutsideIteration chain a)
      (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : final.getMem a = s.getMem a := by
    apply frame a outside
    intro i eq
    have cb := chain.isLt
    have ib := i.isLt
    rcases valid with ⟨lower, upper, aligned⟩
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress, BitVec.toNat_ofNat] at h
    omega
  constructor
  · rw [keep _ (outsideIteration_metadata chain _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact data.levelEq
  · rw [keep _ (outsideIteration_metadata chain _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact data.leafEq
  · exact counter
  · intro i
    rw [keep _ (outsideIteration_metadata chain _ (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideChainWork <;> decide) (by fin_cases i <;> decide)) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [keep _ (outsideIteration_metadata chain _ (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideChainWork <;> decide) (by fin_cases i <;> decide)) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

/-- One complete selected signer upper-leaf iteration, including secret derivation, all
chain HASHes, capture, endpoint storage, and dispatch. -/
theorem sign_selected_iteration (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (message : Reference.Digest)
    (pc : s.pc = 0x1584) (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (settings : CaptureSettings s pointer chain (Reference.digit message chain)) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
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
    KeygenEndpoint.store_endpoint sign 0x1874 (-832) sign_endpoint_code computed chain
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
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
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
    KeygenEndpoint.store_endpoint sign 0x1874 (-832) sign_endpoint_code computed chain
      (Reference.endpoint hash secretKey level tree side chain) computedPC computedData.chainEq computedData.valueEq
  have frame (a : Word) (outside : OutsideIteration chain a) : final.getMem a = s.getMem a := by
    rw [finalFrame a outside.2.1 outside.2.2, computedFrame a outside.1]
  refine ⟨final, steps + 21, cycles + 21, pre.trans post.trace, by omega, by omega, ?_,
    data.iteration s final secretKey pointer level tree side chain valid counter (fun a outside _ => frame a outside),
    endpoint, finalRA.trans computedRA, finalSP.trans computedSP, frame⟩
  simpa [signExtend13] using finalPC

end SigGolfCandidate.Hypertree.Signing
