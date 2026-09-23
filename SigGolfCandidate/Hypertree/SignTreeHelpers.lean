import SigGolfCandidate.Hypertree.SignTreeSettings

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

structure TreeContext (s : MachineState) (secretKey : SecretKey) (level tree : Nat) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyEq : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64

def SignatureWordsOutside (pointer : Nat) (a : Word) : Prop :=
  ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val

def UpperLeafFrame (s final : MachineState) (pointer : Nat) (side selected : Bool) : Prop :=
  ∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a →
    (side = selected → SignatureWordsOutside pointer a) → final.getMem a = s.getMem a

theorem signatureWordsOutside_range (pointer : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : SignatureWordsOutside pointer a := by
  intro chain i eq
  have cb := chain.isLt
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

/-- Regions unchanged by a leaf body, including metadata, input, digits, and stack. -/
theorem outsideLeaf_regions (side : Bool) (a : Word)
    (region : a.toNat < 0x80000 ∨ (0x80400 ≤ a.toNat ∧ a.toNat < 0x80510) ∨
      (0x80600 ≤ a.toNat ∧ a.toNat < 0x80800) ∨ 0x80ae0 ≤ a.toNat)
    (chain : a ≠ 0x80430) (step : a ≠ 0x80438) : OutsideLeafResult side a := by
  refine ⟨⟨⟨?_, ?_, ?_, step⟩, chain, ?_⟩, ?_, ?_⟩
  all_goals (first | intro c i eq | intro i eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals cases side <;> simp [wordAddress, KeygenEndpoint.endpointAddress,
    KeygenSavePublic.wordAddress, Reference.sideNumber] at h <;> omega

theorem UpperLeafFrame.keep (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (valid : CapturePointerValid pointer) (frame : UpperLeafFrame s final pointer side selected)
    (a : Word) (stack : a ≠ 0xffffe0) (outside : OutsideLeafResult side a)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : final.getMem a = s.getMem a :=
  frame a stack outside (fun _ => signatureWordsOutside_range pointer valid a range)

theorem treeContext_after_leaf (s final : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side selected : Bool) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey level tree)
    (frame : UpperLeafFrame s final pointer side selected) : TreeContext final secretKey level tree := by
  have keep := frame.keep s final pointer side selected valid
  constructor
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact data.levelEq
  · intro i
    rw [keep _ (by fin_cases i <;> decide)
      (outsideLeaf_regions side _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [keep _ (by fin_cases i <;> decide)
      (outsideLeaf_regions side _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeSettings_after_leaf (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (message : Reference.Digest) (valid : CapturePointerValid pointer) (settings : TreeSettings s pointer message selected)
    (frame : UpperLeafFrame s final pointer side selected) : TreeSettings final pointer message selected := by
  have keep := frame.keep s final pointer side selected valid
  constructor
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.pointerEq
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.enabled
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word final 0x80600 chain.val (by decide) (by omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · intro eq; have h := congrArg BitVec.toNat eq; simp [wordAddress] at h; omega
    · apply outsideLeaf_regions side
      · simp only [wordAddress, BitVec.toNat_ofNat]; omega
      all_goals intro eq
      all_goals have h := congrArg BitVec.toNat eq
      all_goals simp [wordAddress] at h
      all_goals omega
    · simp only [wordAddress, BitVec.toNat_ofNat]; omega

theorem treeControl_context (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (jump : BitVec 21)
    (data : TreeContext s secretKey level tree) :
    LeafContext (KeygenTreeControl.state s (BitVec.ofNat 12 (Reference.sideNumber side)) jump) secretKey level tree side := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact data.levelEq
  · rw [KeygenTreeControl.mem, if_pos rfl]; cases side <;> rfl
  · intro i
    rw [KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeControl_settings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool)
    (side : BitVec 12) (jump : BitVec 21) (settings : TreeSettings s pointer message selected) :
    TreeSettings (KeygenTreeControl.state s side jump) pointer message selected := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.pointerEq
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.enabled
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word _ 0x80600 chain.val (by decide) (by omega), KeygenTreeControl.mem, if_neg]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · intro eq; have h := congrArg BitVec.toNat eq; simp [wordAddress] at h; omega

end SigGolfCandidate.Hypertree.Signing
