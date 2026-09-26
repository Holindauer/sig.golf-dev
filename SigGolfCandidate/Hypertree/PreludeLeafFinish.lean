import SigGolfCandidate.Hypertree.SignLeafFinish
import SigGolfCandidate.Hypertree.PreludeLeafUnselected
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem leaf_finish (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (pc : s.pc = 0x18c8) (sp : s.getReg .x2 = 0xffffe0) (upper : level ≠ 0)
    (data : LeafData s secretKey level tree side 46)
    (endpoints : EndpointsBefore s hash secretKey level tree side 46) :
    ∃ final, Trace hash signPrelude s 615 710 1 12 final ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, (∀ i : Fin 96, a ≠ wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨final, trace, finalPC, finalSP, root, frame⟩ := KeygenLeaf.compute_return signPrelude hash 0x18c8
    sign_leaf_compress_code sign_leaf_return_code s pc level tree side (Reference.endpoint hash secretKey level tree side)
    data.levelEq data.leafEq data.indexEq (endpoints.words s hash secretKey level tree side)
    (by rw [sp]; decide)
    (by rw [sp]; decide) (by rw [sp]; decide)
    (by rw [sp]; cases side <;> decide)
  refine ⟨final, trace, ?_, ?_, ?_, frame⟩
  · simpa only [sp] using finalPC
  · simpa [sp] using finalSP
  · simpa only [Reference.leafRoot, upper, if_false] using root


theorem sign_selected_leaf_body (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (pc : s.pc = 0x1584) (sp : s.getReg .x2 = 0xffffe0)
    (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side 0) (settings : LeafSignatureSettings s pointer message) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 369 380 final ∧
      instructions ≤ 49881 ∧ cycles ≤ 52552 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      (∀ a, OutsideLeafResult side a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨ready, steps, cycles, pre, stepsBound, cyclesBound, readyPC, readyData, endpoints, signature,
    readyRA, readySP, readyFrame⟩ := sign_selected_leaf_chains hash s secretKey pointer level tree side message pc upper valid data settings
  have rsp : ready.getReg .x2 = 0xffffe0 := readySP.trans sp
  obtain ⟨final, post, finalPC, finalSP, root, finalFrame⟩ := leaf_finish hash ready secretKey level tree side readyPC rsp upper readyData endpoints
  refine ⟨final, steps+615, cycles+710, pre.trans post, by omega, by omega, ?_, finalSP, root, ?_, ?_⟩
  · rw [finalPC, readyFrame _ (by unfold OutsideLeafWork OutsideChainWork; decide)]
    intro chain i eq
    have cb := chain.isLt
    have ib := i.isLt
    rcases valid with ⟨lower, upperBound, aligned⟩
    have h := congrArg BitVec.toNat eq
    simp [wordAddress] at h
    omega
  · intro chain less i
    obtain ⟨hi, ha, hp⟩ := signature_outside_leaf_suffix pointer chain valid side i
    rw [finalFrame _ hi ha hp]
    exact signature chain less i
  · intro a outside captureOutside
    rw [finalFrame a outside.2.1 outside.1.1.2.1 outside.2.2, readyFrame a outside.1 captureOutside]

/-- The other leaf computes its reference root and preserves every signature word. -/
theorem sign_unselected_leaf_body (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (pc : s.pc = 0x1584) (sp : s.getReg .x2 = 0xffffe0)
    (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side 0) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 369 380 final ∧
      instructions ≤ 49881 ∧ cycles ≤ 52552 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideLeafResult side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, steps, cycles, pre, stepsBound, cyclesBound, readyPC, readyData, endpoints,
    readyRA, readySP, readyFrame⟩ := sign_unselected_leaf_chains hash s secretKey pointer level tree side pc valid data ptr unselected
  have rsp : ready.getReg .x2 = 0xffffe0 := readySP.trans sp
  obtain ⟨final, post, finalPC, finalSP, root, finalFrame⟩ := leaf_finish hash ready secretKey level tree side readyPC rsp upper readyData endpoints
  refine ⟨final, steps+615, cycles+710, pre.trans post, by omega, by omega, ?_, finalSP, root, ?_⟩
  · rw [finalPC, readyFrame _ (by unfold OutsideLeafWork OutsideChainWork; decide)]
  · intro a outside
    rw [finalFrame a outside.2.1 outside.1.1.2.1 outside.2.2, readyFrame a outside.1]


end SigGolfCandidate.Hypertree.Signing.Prelude
