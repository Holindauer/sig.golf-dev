import SigGolfCandidate.Hypertree.PreludeLeafEntry
import SigGolfCandidate.Hypertree.SignLeafCall
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
theorem sign_selected_leaf_call (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafContext s secretKey level tree side) (settings : LeafSignatureSettings s pointer message) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 369 380 final ∧
      instructions ≤ 49895 ∧ cycles ≤ 52566 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      (∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  have pre := leafReady_block s pc sp
  have readyPC : (leafReady s).pc = 0x1584 := by
    rw [leafReady_pc s pc sp, data.levelEq, if_neg nonzero]
  have upper : level ≠ 0 := by intro eq; apply nonzero; rw [eq]; rfl
  obtain ⟨final, steps, cycles, body, stepsBound, cyclesBound, finalPC, finalSP, root, signature, frame⟩ :=
    sign_selected_leaf_body hash (leafReady s) secretKey pointer level tree side message readyPC (leafReady_sp s sp)
      upper valid (leafReady_data s secretKey level tree side sp data) (leafReady_settings s pointer message sp settings)
  refine ⟨final, 14+steps, 14+cycles, pre.trace.trans body, by omega, by omega, ?_, ?_, root, signature, ?_⟩
  · rw [finalPC, leafReady_saved s sp]
  · rw [finalSP, sp]
  · intro a stackOutside outside captureOutside
    rw [frame a outside captureOutside, leafReady_frame s sp a stackOutside outside.1.2.1 outside.1.1.2.2.2]

/-- A full unselected signer upper-leaf call preserves all signature words. -/
theorem sign_unselected_leaf_call (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafContext s secretKey level tree side) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 369 380 final ∧
      instructions ≤ 49895 ∧ cycles ≤ 52566 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a → final.getMem a = s.getMem a) := by
  have pre := leafReady_block s pc sp
  have readyPC : (leafReady s).pc = 0x1584 := by
    rw [leafReady_pc s pc sp, data.levelEq, if_neg nonzero]
  have upper : level ≠ 0 := by intro eq; apply nonzero; rw [eq]; rfl
  have readyPtr : (leafReady s).getMem 0x80448 = BitVec.ofNat 64 pointer := by
    rw [leafReady_frame s sp _ (by decide) (by decide) (by decide)]; exact ptr
  have readyUnselected : (leafReady s).getMem 0x80428 ≠ (leafReady s).getMem 0x80420 := by
    rw [leafReady_frame s sp _ (by decide) (by decide) (by decide), leafReady_frame s sp _ (by decide) (by decide) (by decide)]
    exact unselected
  obtain ⟨final, steps, cycles, body, stepsBound, cyclesBound, finalPC, finalSP, root, frame⟩ :=
    sign_unselected_leaf_body hash (leafReady s) secretKey pointer level tree side readyPC (leafReady_sp s sp)
      upper valid (leafReady_data s secretKey level tree side sp data) readyPtr readyUnselected
  refine ⟨final, 14+steps, 14+cycles, pre.trace.trans body, by omega, by omega, ?_, ?_, root, ?_⟩
  · rw [finalPC, leafReady_saved s sp]
  · rw [finalSP, sp]
  · intro a stackOutside outside
    rw [frame a outside, leafReady_frame s sp a stackOutside outside.1.2.1 outside.1.1.2.2.2]

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_selected_leaf_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_selected_leaf_call
/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_unselected_leaf_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_unselected_leaf_call
end SigGolfCandidate.Hypertree.Signing.Prelude
