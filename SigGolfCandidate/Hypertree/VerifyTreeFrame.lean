import SigGolfCandidate.Hypertree.VerifyTreeData

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- The complete tree call changes only its work buffers and two stack frames. -/
def OutsideTreeWork (a : Word) : Prop :=
  OutsideLeafWork a ∧
  (∀ side : Bool, ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80500 i.val) ∧
  a ≠ 0xfffff0 ∧ a ≠ 0xffffe0 ∧ a ≠ 0x80428

theorem outside_tree_low (a : Word) (low : a.toNat < 0x80000) : OutsideTreeWork a := by
  refine ⟨outside_leaf_of_lt a low, ?_, ?_, ?_, ?_, ?_⟩
  · intro side i eq
    have h := congrArg BitVec.toNat eq
    have hi := i.isLt
    cases side <;> simp only [KeygenSavePublic.wordAddress, wordAddress, Reference.sideNumber, Bool.false_eq_true, if_false, if_true, BitVec.toNat_ofNat] at h <;> omega
  · intro i eq
    have h := congrArg BitVec.toNat eq
    have hi := i.isLt
    change a.toNat = (0x80500+8*i.val) % 2^64 at h
    omega
  · intro eq; rw [eq] at low; change 0xfffff0 < 0x80000 at low; omega
  · intro eq; rw [eq] at low; change 0xffffe0 < 0x80000 at low; omega
  · intro eq; rw [eq] at low; change 0x80428 < 0x80000 at low; omega

theorem LayerData.transfer (s final : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (data : LayerData s level tree base side message signature) (bound : base+752 ≤ 0x80000)
    (frame : ∀ a, OutsideTreeWork a → final.getMem a = s.getMem a) :
    LayerData final level tree base side message signature := by
  constructor
  · rw [frame _ (by unfold OutsideTreeWork OutsideLeafWork; decide)]; exact data.levelEq
  · intro i
    rw [frame _ (by fin_cases i <;> unfold OutsideTreeWork OutsideLeafWork <;> decide)]
    exact data.indexEq i
  · rw [frame _ (by unfold OutsideTreeWork OutsideLeafWork; decide)]; exact data.pointerEq
  · rw [frame _ (by unfold OutsideTreeWork OutsideLeafWork; decide)]; exact data.selectorEq
  · intro chain relevant i
    rw [frame _ (outside_tree_low _ ?_)]
    · exact data.valueEq chain relevant i
    · have hc := chain.isLt; have hi := i.isLt
      change (base+16*chain.val+8*i.val) % 2^64 < 0x80000
      omega
  · intro nonzero chain
    rw [getByte_word final 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
      frame _ (by fin_cases chain <;> unfold OutsideTreeWork OutsideLeafWork <;> decide),
      ← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    exact data.digitEq nonzero chain
  · intro i
    rw [frame _ (outside_tree_low _ ?_)]
    · exact data.siblingEq i
    · have hi := i.isLt
      change (base+siblingOffset level+8*i.val) % 2^64 < 0x80000
      unfold siblingOffset
      split <;> omega

theorem tree_entry_context (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (sp : s.getReg .x2 = 0x1000000) (data : LayerData s level tree base side message signature)
    (bound : base+752 ≤ 0x80000) :
    LayerData (VerifyTreeEntry.ready s) level tree base side message signature := by
  apply data.transfer s _ level tree base side message signature bound
  intro a outside
  exact VerifyTreeEntry.frame s sp a outside.2.2.2.1 outside.2.2.2.2.2

end SigGolfCandidate.Hypertree.Verifying
