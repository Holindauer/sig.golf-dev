import SigGolfCandidate.Hypertree.SignIteration

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def LeafSignatureSettings (s : MachineState) (pointer : Nat) (message : Reference.Digest) : Prop :=
  ∀ chain, CaptureSettings s pointer chain (Reference.digit message chain)

def EndpointsBefore (s : MachineState) (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (count : Nat) : Prop := ∀ chain : Reference.Chain, chain.val < count → ∀ i : Fin 2,
      s.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64

def SignatureBefore (s : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (count : Nat) : Prop :=
  ∀ chain : Reference.Chain, chain.val < count →
    CapturedValue s pointer chain ((Reference.signLayer hash secretKey level tree side message).values chain)

def OutsideLeafWork (a : Word) : Prop := OutsideChainWork a ∧ a ≠ 0x80430 ∧
  ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val

theorem iteration_high_frame (s final : MachineState) (pointer : Nat) (current : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a)
    (a : Word) (outside : OutsideIteration current a) (high : 0x80000 ≤ a.toNat) :
    final.getMem a = s.getMem a := by
  apply frame a outside
  intro i eq
  have cb := current.isLt
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem LeafSignatureSettings.iteration (s final : MachineState) (pointer : Nat) (current : Reference.Chain)
    (message : Reference.Digest) (valid : CapturePointerValid pointer)
    (settings : LeafSignatureSettings s pointer message)
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a) :
    LeafSignatureSettings final pointer message := by
  have keep := iteration_high_frame s final pointer current valid frame
  intro chain
  constructor
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).pointerEq
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).enabled
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide),
      keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).selected
  · have cb := chain.isLt
    rw [getByte_word final 0x80600 chain.val (by decide) (by omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact (settings chain).digitEq
    · apply outsideIteration_metadata current
      · simp only [wordAddress, BitVec.toNat_ofNat]; omega
      · unfold OutsideChainWork
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals (first | intro j eq | intro eq)
        all_goals have h := congrArg BitVec.toNat eq
        all_goals simp [wordAddress] at h
        all_goals omega
      · intro eq
        have h := congrArg BitVec.toNat eq
        simp [wordAddress] at h
        omega
    · simp only [wordAddress, BitVec.toNat_ofNat]; omega

theorem endpoint_distinct (chain other : Reference.Chain) (i j : Fin 2) (different : chain ≠ other) :
    KeygenEndpoint.endpointAddress chain.val i.val ≠ KeygenEndpoint.endpointAddress other.val j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := other.isLt
  have ib := i.isLt
  have jb := j.isLt
  have ne : chain.val ≠ other.val := by intro same; exact different (Fin.ext same)
  simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
  omega

theorem endpoint_outside_chain (chain : Reference.Chain) (i : Fin 2) :
    OutsideChainWork (KeygenEndpoint.endpointAddress chain.val i.val) ∧
      KeygenEndpoint.endpointAddress chain.val i.val ≠ 0x80430 := by
  have cb := chain.isLt
  have ib := i.isLt
  unfold OutsideChainWork
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals (first | intro j eq | intro eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp [KeygenEndpoint.endpointAddress, wordAddress] at h
  all_goals omega

theorem signature_distinct (pointer : Nat) (chain other : Reference.Chain) (i j : Fin 2)
    (valid : CapturePointerValid pointer) (different : chain ≠ other) :
    wordAddress (pointer + 16 * chain.val) i.val ≠ wordAddress (pointer + 16 * other.val) j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := other.isLt
  have ib := i.isLt
  have jb := j.isLt
  have ne : chain.val ≠ other.val := by intro same; exact different (Fin.ext same)
  rcases valid with ⟨lower, upper, aligned⟩
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem signature_outside_iteration (pointer : Nat) (chain current : Reference.Chain)
    (valid : CapturePointerValid pointer) (i : Fin 2) :
    OutsideIteration current (wordAddress (pointer + 16 * chain.val) i.val) := by
  refine ⟨capture_output_outside_work pointer chain valid i, (signature_outside_endpoint pointer chain valid i).1, ?_⟩
  intro j eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := current.isLt
  have ib := i.isLt
  have jb := j.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp only [wordAddress, KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
  omega

end SigGolfCandidate.Hypertree.Signing
