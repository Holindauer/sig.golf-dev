import SigGolfCandidate.Hypertree.SignLayerPrepare

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

theorem outsideTreeWork_metadata (a : Word)
    (range : (0x80400 ≤ a.toNat ∧ a.toNat < 0x80428) ∨ (0x80440 ≤ a.toNat ∧ a.toNat < 0x80450)) :
    OutsideTreeWork a := by
  have chain : a ≠ 0x80430 := by intro eq; rw [eq] at range; revert range; decide
  have step : a ≠ 0x80438 := by intro eq; rw [eq] at range; revert range; decide
  refine ⟨⟨outsideLeaf_regions false a (by omega) chain step,
    outsideLeaf_regions true a (by omega) chain step,?_,?_,?_⟩,?_⟩
  · intro eq; rw [eq] at range; revert range; decide
  · intro eq; rw [eq] at range; revert range; decide
  · intro eq; rw [eq] at range; revert range; decide
  · intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    have := i.isLt
    omega

theorem outsideLayer_high (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (high : 0x80000 ≤ a.toNat) : OutsideLayer pointer level a := by
  rcases valid with ⟨lower,upper,aligned⟩
  right
  unfold layerBytes
  split <;> omega

theorem advance_low_frame (s : MachineState) (a : Word) (low : a.toNat < 0x80000) :
    (advanceState s).getMem a = s.getMem a := by
  rw [advanceState_mem,if_neg (low_ne_high _ _ low (by decide)),if_neg (low_ne_high _ _ low (by decide))]

theorem LayerStored.frame (s final : MachineState) (pointer level : Nat) (signature : Reference.LayerSignature)
    (valid : CapturePointerValid pointer) (stored : LayerStored s pointer level signature)
    (frame : ∀ a, a.toNat < 0x80000 → final.getMem a = s.getMem a) : LayerStored final pointer level signature := by
  unfold LayerStored at *
  split at stored <;> rename_i h
  all_goals simp only [h,if_true,if_false]
  · constructor
    · intro i
      rw [frame _ (signature_word_low pointer valid 0 i)]
      exact stored.1 i
    · intro i
      have low : (wordAddress (pointer+16) i.val).toNat < 0x80000 := by
        rcases valid with ⟨lower,upper,aligned⟩
        have := i.isLt
        simp only [wordAddress,BitVec.toNat_ofNat]; omega
      rw [frame _ low]; exact stored.2 i
  · constructor
    · intro chain i
      rw [frame _ (signature_word_low pointer valid chain i)]; exact stored.1 chain i
    · intro i
      have low : (wordAddress (pointer+736) i.val).toNat < 0x80000 := by
        rcases valid with ⟨lower,upper,aligned⟩
        have := i.isLt
        simp only [wordAddress,BitVec.toNat_ofNat]; omega
      rw [frame _ low]; exact stored.2 i

end SigGolfCandidate.Hypertree.Signing
