import SigGolfCandidate.Hypertree.SignTreeSettings
import SigGolfCandidate.Hypertree.PreludeLeafCall
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem sign_upper_leaf_call (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side selected : Bool) (message : Reference.Digest) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafContext s secretKey level tree side) (settings : TreeSettings s pointer message selected) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 369 380 final ∧
      instructions ≤ 49895 ∧ cycles ≤ 52566 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (side = selected → SignatureBefore final hash secretKey pointer level tree side message 46) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a →
        (side = selected → ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) →
          final.getMem a = s.getMem a) := by
  by_cases same : side = selected
  · subst side
    obtain ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, signature, frame⟩ :=
      sign_selected_leaf_call hash s secretKey pointer level tree selected message pc sp nonzero valid data
        (settings.selected s secretKey pointer level tree message selected data)
    exact ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, fun _ => signature,
      fun a stack outside capture => frame a stack outside (capture rfl)⟩
  · obtain ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, frame⟩ :=
      sign_unselected_leaf_call hash s secretKey pointer level tree side pc sp nonzero valid data settings.pointerEq
        (settings.unselected s secretKey pointer level tree message side selected data same)
    exact ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, fun eq => (same eq).elim,
      fun a stack outside _ => frame a stack outside⟩

theorem sign_tree_left_code : KeygenTreeControl.Code signPrelude 0x13d0 0 364 := by decide
theorem sign_tree_right_code : KeygenTreeControl.Code signPrelude 0x13e4 1 344 := by decide


end SigGolfCandidate.Hypertree.Signing.Prelude
