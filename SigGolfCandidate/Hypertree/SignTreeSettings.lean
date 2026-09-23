import SigGolfCandidate.Hypertree.SignLeafCall
import SigGolfCandidate.Hypertree.SignSiblingRun
import SigGolfCandidate.Hypertree.KeygenTreeControl

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure TreeSettings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selectorEq : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)
  digits : ∀ chain : Reference.Chain,
    s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val

theorem TreeSettings.selected (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (settings : TreeSettings s pointer message selected)
    (data : LeafContext s secretKey level tree selected) : LeafSignatureSettings s pointer message := by
  intro chain
  exact ⟨settings.pointerEq, settings.enabled, data.leafEq.trans settings.selectorEq.symm, settings.digits chain⟩

theorem TreeSettings.unselected (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (side selected : Bool) (settings : TreeSettings s pointer message selected)
    (data : LeafContext s secretKey level tree side) (different : side ≠ selected) :
    s.getMem 0x80428 ≠ s.getMem 0x80420 := by
  rw [data.leafEq, settings.selectorEq]
  cases side <;> cases selected <;> simp_all [Reference.sideNumber]

/-- Uniform upper-leaf call interface, with signature output exactly when this leaf is selected. -/
theorem sign_upper_leaf_call (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side selected : Bool) (message : Reference.Digest) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafContext s secretKey level tree side) (settings : TreeSettings s pointer message selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 369 380 final ∧
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

theorem sign_tree_left_code : KeygenTreeControl.Code sign 0x13d0 0 364 := by decide
theorem sign_tree_right_code : KeygenTreeControl.Code sign 0x13e4 1 344 := by decide

end SigGolfCandidate.Hypertree.Signing
