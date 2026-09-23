import SigGolfCandidate.Hypertree.SignSiblingRefine

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def OutsideTreeLeaves (a : Word) : Prop :=
  OutsideLeafResult false a ∧ OutsideLeafResult true a ∧
    a ≠ 0x80428 ∧ a ≠ 0xffffe0 ∧ a ≠ 0xfffff0

theorem signature_word_low (pointer : Nat) (valid : CapturePointerValid pointer)
    (chain : Reference.Chain) (i : Fin 2) : (wordAddress (pointer + 16 * chain.val) i.val).toNat < 0x80000 := by
  rcases valid with ⟨lower, upper, aligned⟩
  have cb := chain.isLt
  have ib := i.isLt
  simp only [wordAddress, BitVec.toNat_ofNat]
  omega

theorem low_ne_high (a b : Word) (low : a.toNat < 0x80000) (high : 0x80000 ≤ b.toNat) : a ≠ b := by
  intro eq; rw [eq] at low; omega

/-- Both actual upper-leaf calls produce their public roots and exactly the selected
signature vector, before authentication-node copying and the parent hash. -/
theorem sign_upper_tree_leaves (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : TreeContext s secretKey level tree) (settings : TreeSettings s pointer message selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 738 760 final ∧
      instructions ≤ 99802 ∧ cycles ≤ 105144 ∧ final.pc = 0x13f8 ∧ final.getReg .x2 = 0xfffff0 ∧
      final.getMem 0xfffff0 = s.getReg .x1 ∧ TreeContext final secretKey level tree ∧
      TreeSettings final pointer message selected ∧
      (∀ side : Bool, ∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      SignatureBefore final hash secretKey pointer level tree selected message 46 ∧
      (∀ a, OutsideTreeLeaves a → SignatureWordsOutside pointer a → final.getMem a = s.getMem a) := by
  let ready := treeLeftState s
  have pre := treeLeft_block s pc sp
  have readyPC := treeLeft_pc s pc
  have readySP := treeLeft_sp s sp
  have readyRA := treeLeft_ra s pc
  have readyContext := treeLeft_context s secretKey level tree sp data
  have readySettings := treeLeft_settings s pointer message selected sp settings
  obtain ⟨left, leftSteps, leftCycles, leftTrace, leftStepsBound, leftCyclesBound, leftPC, leftSP, leftRoot,
    leftSignature, leftFrame⟩ := sign_upper_leaf_call hash ready secretKey pointer level tree false selected message
      readyPC readySP nonzero valid readyContext readySettings
  have leftRet : left.pc = 0x13e4 := by rw [leftPC, readyRA]; decide
  have leftStack : left.getReg .x2 = 0xfffff0 := leftSP.trans readySP
  have readyTree : TreeContext ready secretKey level tree := ⟨readyContext.levelEq, readyContext.indexEq, readyContext.secretKeyEq⟩
  have leftContext := treeContext_after_leaf ready left secretKey pointer level tree false selected valid readyTree leftFrame
  have leftSettings := treeSettings_after_leaf ready left pointer false selected message valid readySettings leftFrame
  let rightReady := KeygenTreeControl.state left 1 344
  have rightPre := KeygenTreeControl.block sign 0x13e4 1 344 sign_tree_right_code left leftRet
  have rightReadyPC : rightReady.pc = 0x154c := by rw [KeygenTreeControl.pc, leftRet]; rfl
  have rightReadySP : rightReady.getReg .x2 = 0xfffff0 := (KeygenTreeControl.sp left 1 344).trans leftStack
  have rightReadyRA : rightReady.getReg .x1 = 0x13f8 := by rw [KeygenTreeControl.ra, leftRet]; rfl
  have rightContext := treeControl_context left secretKey level tree true 344 leftContext
  have rightSettings := treeControl_settings left pointer message selected 1 344 leftSettings
  obtain ⟨right, rightSteps, rightCycles, rightTrace, rightStepsBound, rightCyclesBound, rightPC, rightSP, rightRoot,
    rightSignature, rightFrame⟩ := sign_upper_leaf_call hash rightReady secretKey pointer level tree true selected message
      rightReadyPC rightReadySP nonzero valid rightContext rightSettings
  have rightRet : right.pc = 0x13f8 := by rw [rightPC, rightReadyRA]; decide
  have rightStack : right.getReg .x2 = 0xfffff0 := rightSP.trans rightReadySP
  have rightTree : TreeContext rightReady secretKey level tree := ⟨rightContext.levelEq, rightContext.indexEq, rightContext.secretKeyEq⟩
  have finalContext := treeContext_after_leaf rightReady right secretKey pointer level tree true selected valid rightTree rightFrame
  have finalSettings := treeSettings_after_leaf rightReady right pointer true selected message valid rightSettings rightFrame
  have frame (a : Word) (outside : OutsideTreeLeaves a) (captureOutside : SignatureWordsOutside pointer a) :
      right.getMem a = s.getMem a := by
    rw [rightFrame a outside.2.2.2.1 outside.2.1 (fun _ => captureOutside), KeygenTreeControl.mem, if_neg outside.2.2.1,
      leftFrame a outside.2.2.2.1 outside.1 (fun _ => captureOutside), treeLeft_frame s sp a outside.2.2.2.2 outside.2.2.1]
  have saved : right.getMem 0xfffff0 = s.getReg .x1 := by
    rw [rightFrame _ (by decide) (outsideLeaf_regions true _ (by decide) (by decide) (by decide))
      (fun _ => signatureWordsOutside_range pointer valid _ (by decide)), KeygenTreeControl.mem, if_neg (by decide),
      leftFrame _ (by decide) (outsideLeaf_regions false _ (by decide) (by decide) (by decide))
      (fun _ => signatureWordsOutside_range pointer valid _ (by decide)), treeLeft_saved s sp]
  refine ⟨right, 12 + leftSteps + rightSteps, 12 + leftCycles + rightCycles, ?_, by omega, by omega,
    rightRet, rightStack, saved, finalContext, finalSettings, ?_, ?_, frame⟩
  · convert pre.trace.trans (leftTrace.trans (rightPre.trace.trans rightTrace)) using 1 <;> omega
  · intro side i
    cases side
    · rw [rightFrame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> unfold OutsideLeafResult OutsideLeafWork OutsideChainWork <;> decide)
        (fun _ => signatureWordsOutside_range pointer valid _ (by fin_cases i <;> decide)),
        KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
      exact leftRoot i
    · exact rightRoot i
  · cases selected
    · have old := leftSignature rfl
      intro chain less i
      have low := signature_word_low pointer valid chain i
      rw [rightFrame _ (low_ne_high _ _ low (by decide))
        (outsideLeaf_regions true _ (Or.inl low) (low_ne_high _ _ low (by decide)) (low_ne_high _ _ low (by decide)))
        (by intro eq; cases eq), KeygenTreeControl.mem, if_neg (low_ne_high _ _ low (by decide))]
      exact old chain less i
    · exact rightSignature rfl

end SigGolfCandidate.Hypertree.Signing
