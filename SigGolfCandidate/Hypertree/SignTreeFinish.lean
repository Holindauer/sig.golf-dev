import SigGolfCandidate.Hypertree.SignTreeLeaves

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def OutsideTreeWork (a : Word) : Prop := OutsideTreeLeaves a ∧
  ∀ i : Fin 2, a ≠ wordAddress 0x80500 i.val

def SiblingWordsOutside (pointer : Nat) (a : Word) : Prop :=
  ∀ i : Fin 2, a ≠ wordAddress (pointer + 736) i.val

def UpperLayerStored (s : MachineState) (pointer : Nat) (signature : Reference.LayerSignature) : Prop :=
  (∀ chain : Reference.Chain, CapturedValue s pointer chain (signature.values chain)) ∧
    SiblingStored s pointer signature.sibling

theorem siblingWordsOutside_range (pointer : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : SiblingWordsOutside pointer a := by
  intro i eq
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem signature_outside_sibling (pointer : Nat) (valid : CapturePointerValid pointer)
    (chain : Reference.Chain) (i : Fin 2) : SiblingWordsOutside pointer (wordAddress (pointer + 16 * chain.val) i.val) := by
  intro j eq
  have cb := chain.isLt
  have ib := i.isLt
  have jb := j.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem low_outside_node (a : Word) (low : a.toNat < 0x80000) :
    (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
    (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
    (∀ i : Fin 2, a ≠ wordAddress 0x80500 i.val) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i eq
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp [wordAddress] at h
  all_goals omega

/-- The entire actual signer upper tree call produces the reference parent root and
complete reference layer signature, with exact739oraclecalls/761compressions. -/
theorem sign_upper_tree (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : TreeContext s secretKey level tree) (settings : TreeSettings s pointer message selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 739 761 final ∧
      instructions ≤ 99910 ∧ cycles ≤ 105259 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey level tree).extractLsb' (64*i.val) 64) ∧
      UpperLayerStored final pointer (Reference.signLayer hash secretKey level tree selected message) ∧
      (∀ a, OutsideTreeWork a → SignatureWordsOutside pointer a → SiblingWordsOutside pointer a → final.getMem a = s.getMem a) := by
  obtain ⟨leaves, leafSteps, leafCycles, pre, leafStepsBound, leafCyclesBound, leavesPC, leavesSP, saved,
    leavesContext, leavesSettings, roots, signature, leavesFrame⟩ :=
    sign_upper_tree_leaves hash s secretKey pointer level tree message selected pc sp nonzero valid data settings
  have levelNonzero : leaves.getMem 0x80400 ≠ 0 := by rw [leavesContext.levelEq]; exact nonzero
  obtain ⟨prepared, siblingTrace, preparedPC, sibling, preparedSP, siblingFrame⟩ := sign_upper_sibling leaves pointer selected
    (Reference.leafRoot hash secretKey level tree (!selected)) leavesPC valid leavesSettings.pointerEq leavesSettings.enabled
    levelNonzero leavesSettings.selectorEq (roots (!selected))
  have keep (a : Word) (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : prepared.getMem a = leaves.getMem a :=
    siblingFrame a (siblingWordsOutside_range pointer valid a range)
  have levelEq : prepared.getMem 0x80400 = BitVec.ofNat 64 level := by rw [keep _ (by decide)]; exact leavesContext.levelEq
  have indexEq : ∀ i : Fin 3, prepared.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i; rw [keep _ (by fin_cases i <;> decide)]; exact leavesContext.indexEq i
  have children : ∀ i : Fin 4, prepared.getMem (wordAddress 0x80520 i.val) =
      if i.val < 2 then (Reference.leafRoot hash secretKey level tree false).extractLsb' (64*i.val) 64
      else (Reference.leafRoot hash secretKey level tree true).extractLsb' (64*(i.val-2)) 64 := by
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
    sign_node_return_code prepared preparedPC level tree (Reference.leafRoot hash secretKey level tree false)
    (Reference.leafRoot hash secretKey level tree true) levelEq indexEq children
    (by rw [psp]; decide) (by rw [psp]; decide) (by rw [psp]; decide) (by rw [psp]; decide)
  have lowFrame (a : Word) (low : a.toNat < 0x80000) : final.getMem a = prepared.getMem a := by
    obtain ⟨hi, ha, hc⟩ := low_outside_node a low
    exact finalFrame a hi ha hc
  refine ⟨final, leafSteps+108, leafCycles+115, ?_, by omega, by omega, ?_, ?_, root, ?_, ?_⟩
  · convert pre.trans (siblingTrace.trace.trans post) using 1
  · rw [finalPC, psp, psaved]
  · rw [finalSP, psp, sp]; rfl
  · constructor
    · intro chain i
      rw [lowFrame _ (signature_word_low pointer valid chain i),
        siblingFrame _ (signature_outside_sibling pointer valid chain i)]
      exact signature chain chain.isLt i
    · intro i
      have low : (wordAddress (pointer+736) i.val).toNat < 0x80000 := by
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

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_upper_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_upper_tree

end SigGolfCandidate.Hypertree.Signing
