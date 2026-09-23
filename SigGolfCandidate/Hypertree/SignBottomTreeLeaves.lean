import SigGolfCandidate.Hypertree.SignBottomValue

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Both actual bottom-leaf calls produce their public roots and exactly the selected
secret preimage, before authentication-node copying and the parent hash. -/
theorem sign_bottom_tree_leaves (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (valid : CapturePointerValid pointer)
    (data : TreeContext s secretKey 0 tree) (settings : BottomTreeSettings s pointer selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 4 4 final ∧
      instructions ≤ 430 ∧ cycles ≤ 458 ∧ final.pc = 0x13f8 ∧ final.getReg .x2 = 0xfffff0 ∧
      final.getMem 0xfffff0 = s.getReg .x1 ∧ TreeContext final secretKey 0 tree ∧
      BottomTreeSettings final pointer selected ∧
      (∀ side : Bool, ∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey 0 tree side).extractLsb' (64*i.val) 64) ∧
      CapturedValue final pointer 0 (Reference.secret hash secretKey 0 tree selected 0) ∧
      (∀ a, OutsideTreeLeaves a → (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → final.getMem a = s.getMem a) := by
  let ready := treeLeftState s
  have pre := treeLeft_block s pc sp
  have readyPC := treeLeft_pc s pc
  have readySP := treeLeft_sp s sp
  have readyRA := treeLeft_ra s pc
  have readyContext := treeLeft_context s secretKey 0 tree sp data
  have readySettings := treeLeft_bottom_settings s pointer selected sp settings
  obtain ⟨left, leftSteps, leftCycles, leftTrace, leftStepsBound, leftCyclesBound, leftPC, leftSP, leftRoot,
    leftLow, leftFrame⟩ := sign_bottom_leaf_call hash ready secretKey pointer tree false
      readyPC readySP valid readySettings.pointerEq readyContext
  have leftRet : left.pc = 0x13e4 := by rw [leftPC, readyRA]; decide
  have leftStack : left.getReg .x2 = 0xfffff0 := leftSP.trans readySP
  have readyTree : TreeContext ready secretKey 0 tree := ⟨readyContext.levelEq, readyContext.indexEq, readyContext.secretKeyEq⟩
  have leftContext := treeContext_after_bottom_leaf ready left secretKey pointer tree false valid readyTree leftFrame
  have leftSettings := bottomSettings_after_leaf ready left pointer false selected valid readySettings leftFrame
  let rightReady := KeygenTreeControl.state left 1 344
  have rightPre := KeygenTreeControl.block sign 0x13e4 1 344 sign_tree_right_code left leftRet
  have rightReadyPC : rightReady.pc = 0x154c := by rw [KeygenTreeControl.pc, leftRet]; rfl
  have rightReadySP : rightReady.getReg .x2 = 0xfffff0 := (KeygenTreeControl.sp left 1 344).trans leftStack
  have rightReadyRA : rightReady.getReg .x1 = 0x13f8 := by rw [KeygenTreeControl.ra, leftRet]; rfl
  have rightContext := treeControl_context left secretKey 0 tree true 344 leftContext
  have rightSettings := treeControl_bottom_settings left pointer selected 1 344 leftSettings
  obtain ⟨right, rightSteps, rightCycles, rightTrace, rightStepsBound, rightCyclesBound, rightPC, rightSP, rightRoot,
    rightLow, rightFrame⟩ := sign_bottom_leaf_call hash rightReady secretKey pointer tree true
      rightReadyPC rightReadySP valid rightSettings.pointerEq rightContext
  have rightRet : right.pc = 0x13f8 := by rw [rightPC, rightReadyRA]; decide
  have rightStack : right.getReg .x2 = 0xfffff0 := rightSP.trans rightReadySP
  have rightTree : TreeContext rightReady secretKey 0 tree := ⟨rightContext.levelEq, rightContext.indexEq, rightContext.secretKeyEq⟩
  have finalContext := treeContext_after_bottom_leaf rightReady right secretKey pointer tree true valid rightTree rightFrame
  have finalSettings := bottomSettings_after_leaf rightReady right pointer true selected valid rightSettings rightFrame
  have frame (a : Word) (outside : OutsideTreeLeaves a) (captureOutside : ∀ i : Fin 2, a ≠ wordAddress pointer i.val) :
      right.getMem a = s.getMem a := by
    rw [rightFrame a outside.2.2.2.1 outside.2.1.1.2.1 outside.2.1.1.1.2.2.2
      (bottomOutside_of_leafResult true a outside.2.1) captureOutside,
      KeygenTreeControl.mem, if_neg outside.2.2.1,
      leftFrame a outside.2.2.2.1 outside.1.1.2.1 outside.1.1.1.2.2.2
      (bottomOutside_of_leafResult false a outside.1) captureOutside,
      treeLeft_frame s sp a outside.2.2.2.2 outside.2.2.1]
  have saved : right.getMem 0xfffff0 = s.getReg .x1 := by
    rw [BottomLeafFrame.keep rightReady right pointer true valid rightFrame _ (by decide) (by decide) (by decide)
      (by unfold OutsideBottomWork; decide) (by decide), KeygenTreeControl.mem, if_neg (by decide),
      BottomLeafFrame.keep ready left pointer false valid leftFrame _ (by decide) (by decide) (by decide)
      (by unfold OutsideBottomWork; decide) (by decide), treeLeft_saved s sp]
  refine ⟨right, 12 + leftSteps + rightSteps, 12 + leftCycles + rightCycles, ?_, by omega, by omega,
    rightRet, rightStack, saved, finalContext, finalSettings, ?_, ?_, frame⟩
  · convert pre.trace.trans (leftTrace.trans (rightPre.trace.trans rightTrace)) using 1 <;> omega
  · intro side i
    cases side
    · rw [BottomLeafFrame.keep rightReady right pointer true valid rightFrame _
        (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> unfold OutsideBottomWork <;> decide) (by fin_cases i <;> decide),
        KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
      exact leftRoot i
    · exact rightRoot i
  · cases selected
    · have old := bottom_selected_value ready left hash secretKey pointer tree false valid readyContext readySettings leftLow
      intro i
      have low := signature_word_low pointer valid 0 i
      rw [bottom_unselected_low rightReady right hash secretKey pointer tree true false rightContext rightSettings
        (by decide) rightLow _ low, KeygenTreeControl.mem, if_neg (low_ne_high _ _ low (by decide))]
      exact old i
    · exact bottom_selected_value rightReady right hash secretKey pointer tree true valid rightContext rightSettings rightLow

end SigGolfCandidate.Hypertree.Signing
