import SigGolfCandidate.Hypertree.SignBottomSibling

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def BottomSiblingWordsOutside (pointer : Nat) (a : Word) : Prop :=
  ∀ i : Fin 2, a ≠ wordAddress (pointer + 16) i.val

def BottomLayerStored (s : MachineState) (pointer : Nat) (signature : Reference.LayerSignature) : Prop :=
  CapturedValue s pointer 0 (signature.values 0) ∧
    BottomSiblingStored s pointer signature.sibling

theorem bottomSiblingWordsOutside_range (pointer : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : BottomSiblingWordsOutside pointer a := by
  intro i eq
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem bottom_signature_outside_sibling (pointer : Nat) (valid : CapturePointerValid pointer)
    (i : Fin 2) : BottomSiblingWordsOutside pointer (wordAddress pointer i.val) := by
  intro j eq
  have ib := i.isLt
  have jb := j.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

/-- The entire actual signer bottom tree call produces the reference parent root and
complete reference layer signature, with exactly five oracle calls and compressions. -/
theorem sign_bottom_tree (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (valid : CapturePointerValid pointer)
    (data : TreeContext s secretKey 0 tree) (settings : BottomTreeSettings s pointer selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 5 5 final ∧
      instructions ≤ 537 ∧ cycles ≤ 572 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey 0 tree).extractLsb' (64*i.val) 64) ∧
      BottomLayerStored final pointer (Reference.signLayer hash secretKey 0 tree selected 0) ∧
      (∀ a, OutsideTreeWork a → (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → BottomSiblingWordsOutside pointer a → final.getMem a = s.getMem a) := by
  obtain ⟨leaves, leafSteps, leafCycles, pre, leafStepsBound, leafCyclesBound, leavesPC, leavesSP, saved,
    leavesContext, leavesSettings, roots, signature, leavesFrame⟩ :=
    sign_bottom_tree_leaves hash s secretKey pointer tree selected pc sp valid data settings
  have levelZero : leaves.getMem 0x80400 = 0 := leavesContext.levelEq
  obtain ⟨prepared, siblingTrace, preparedPC, sibling, preparedSP, siblingFrame⟩ := sign_bottom_sibling leaves pointer selected
    (Reference.leafRoot hash secretKey 0 tree (!selected)) leavesPC valid leavesSettings.pointerEq leavesSettings.enabled
    levelZero leavesSettings.selectorEq (roots (!selected))
  have keep (a : Word) (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : prepared.getMem a = leaves.getMem a :=
    siblingFrame a (bottomSiblingWordsOutside_range pointer valid a range)
  have levelEq : prepared.getMem 0x80400 = BitVec.ofNat 64 0 := by rw [keep _ (by decide)]; exact leavesContext.levelEq
  have indexEq : ∀ i : Fin 3, prepared.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i; rw [keep _ (by fin_cases i <;> decide)]; exact leavesContext.indexEq i
  have children : ∀ i : Fin 4, prepared.getMem (wordAddress 0x80520 i.val) =
      if i.val < 2 then (Reference.leafRoot hash secretKey 0 tree false).extractLsb' (64*i.val) 64
      else (Reference.leafRoot hash secretKey 0 tree true).extractLsb' (64*(i.val-2)) 64 := by
    intro i
    rw [keep _ (by fin_cases i <;> decide)]
    fin_cases i
    · exact roots false 0
    · exact roots false 1
    · exact roots true 0
    · exact roots true 1
  have psp : prepared.getReg .x2 = 0xfffff0 := preparedSP.trans leavesSP
  have psaved : prepared.getMem 0xfffff0 = s.getReg .x1 := by rw [keep _ (by decide), saved]
  obtain ⟨final, post, finalPC, finalSP, root, finalFrame⟩ := KeygenNode.compute_return sign hash 0x1460 sign_node_body_code
    sign_node_return_code prepared preparedPC 0 tree (Reference.leafRoot hash secretKey 0 tree false)
    (Reference.leafRoot hash secretKey 0 tree true) levelEq indexEq children
    (by rw [psp]; decide) (by rw [psp]; decide) (by rw [psp]; decide) (by rw [psp]; decide)
  have lowFrame (a : Word) (low : a.toNat < 0x80000) : final.getMem a = prepared.getMem a := by
    obtain ⟨hi, ha, hc⟩ := low_outside_node a low
    exact finalFrame a hi ha hc
  refine ⟨final, leafSteps+107, leafCycles+114, ?_, by omega, by omega, ?_, ?_, root, ?_, ?_⟩
  · convert pre.trans (siblingTrace.trace.trans post) using 1
  · rw [finalPC, psp, psaved]
  · rw [finalSP, psp, sp]; rfl
  · constructor
    · intro i
      change final.getMem (wordAddress pointer i.val) = _
      have low : (wordAddress pointer i.val).toNat < 0x80000 := by
        simpa using signature_word_low pointer valid 0 i
      rw [lowFrame _ low,
        siblingFrame _ (bottom_signature_outside_sibling pointer valid i)]
      exact signature i
    · intro i
      have low : (wordAddress (pointer+16) i.val).toNat < 0x80000 := by
        rcases valid with ⟨lower, upper, aligned⟩
        have ib := i.isLt
        simp only [wordAddress, BitVec.toNat_ofNat]
        omega
      rw [lowFrame _ low]
      exact sibling i
  · intro a outside signatureOutside siblingOutside
    have inputOutside : ∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val :=
      fun i => outside.1.1.2.1 ⟨i.val, by have := i.isLt; omega⟩
    rw [finalFrame a inputOutside outside.1.1.1.1.2.1 outside.2,
      siblingFrame a siblingOutside, leavesFrame a outside.1 signatureOutside]

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_bottom_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_bottom_tree

end SigGolfCandidate.Hypertree.Signing
