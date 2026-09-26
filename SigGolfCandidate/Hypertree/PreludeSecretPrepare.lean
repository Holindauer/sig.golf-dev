import SigGolfCandidate.Hypertree.SignSecretPrepare
import SigGolfCandidate.Hypertree.PreludeSites
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
theorem prelude_step_zero_code : KeygenStepZero.Code signPrelude 0x1688 := by decide
theorem sign_secret_prepare (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (data : LeafData s secretKey level tree side chain.val) :
    ∃ final, Trace hash signPrelude s 93 100 1 1 final ∧ final.pc = 0x1698 ∧
      ChainData final level tree side chain 0 (Reference.secret hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨secret, pre, secretPC, secretWords, ra, sp, frame⟩ := KeygenSecret.compute signPrelude hash 0x1584 sign_upper_secret_code
    s pc level tree side chain secretKey data.levelEq data.leafEq data.chainEq data.indexEq data.secretKeyEq
  have reset := KeygenStepZero.block signPrelude 0x1688 prelude_step_zero_code secret secretPC
  have keep (a : Word) (outside : OutsideChainWork a) : (KeygenStepZero.state secret).getMem a = s.getMem a := by
    rw [KeygenStepZero.mem, if_neg outside.2.2.2, frame a outside.1 outside.2.1 outside.2.2.1]
  refine ⟨KeygenStepZero.state secret, pre.trans reset.trace, ?_, ?_,
    (KeygenStepZero.stack secret).1.trans ra, (KeygenStepZero.stack secret).2.trans sp, keep⟩
  · rw [KeygenStepZero.pc, secretPC]; rfl
  · constructor
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.levelEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.leafEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.chainEq
    · rw [KeygenStepZero.mem, if_pos rfl]; rfl
    · intro i
      rw [keep _ (by fin_cases i <;> unfold OutsideChainWork <;> decide)]
      exact data.indexEq i
    · intro i
      rw [KeygenStepZero.mem, if_neg (by fin_cases i <;> decide)]
      exact secretWords i

/-- A full selected signer chain derives its secret, computes the endpoint, and writes the
reference signature checkpoint, using exactly eight compression calls. -/
theorem sign_selected_chain (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (message : Reference.Digest)
    (pc : s.pc = 0x1584) (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (settings : CaptureSettings s pointer chain (Reference.digit message chain)) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 8 8 final ∧
      instructions ≤ 1050 ∧ cycles ≤ 1106 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      CapturedValue final pointer chain ((Reference.signLayer hash secretKey level tree side message).values chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, readyPC, readyData, readyRA, readySP, readyFrame⟩ :=
    sign_secret_prepare hash s secretKey level tree side chain pc data
  have readySettings := settings.frame s ready pointer chain _ valid (fun a outside _ => readyFrame a outside)
  obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData, captured,
    finalRA, finalSP, finalFrame⟩ := sign_chain_captured_endpoint hash ready secretKey pointer level tree side chain message
      readyPC upper valid readyData readySettings
  refine ⟨final, 93 + steps, 100 + cycles, pre.trans tail, by omega, by omega,
    finalPC, finalData, captured, finalRA.trans readyRA, finalSP.trans readySP, ?_⟩
  intro a outside captureOutside
  rw [finalFrame a outside captureOutside, readyFrame a outside]

/-- The other leaf's full chain also costs exactly eight compressions and preserves the signature. -/
theorem sign_unselected_chain (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 8 8 final ∧
      instructions ≤ 1050 ∧ cycles ≤ 1106 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, readyPC, readyData, readyRA, readySP, readyFrame⟩ :=
    sign_secret_prepare hash s secretKey level tree side chain pc data
  have readyPtr : ready.getMem 0x80448 = BitVec.ofNat 64 pointer := by
    rw [readyFrame _ (by unfold OutsideChainWork; decide)]; exact ptr
  have readyUnselected : ready.getMem 0x80428 ≠ ready.getMem 0x80420 := by
    rw [readyFrame _ (by unfold OutsideChainWork; decide), readyFrame _ (by unfold OutsideChainWork; decide)]
    exact unselected
  obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData,
    finalRA, finalSP, finalFrame⟩ := sign_chain_unselected_endpoint hash ready secretKey pointer level tree side chain
      readyPC valid readyPtr readyData readyUnselected
  refine ⟨final, 93 + steps, 100 + cycles, pre.trans tail, by omega, by omega,
    finalPC, finalData, finalRA.trans readyRA, finalSP.trans readySP, ?_⟩
  intro a outside
  rw [finalFrame a outside, readyFrame a outside]


end SigGolfCandidate.Hypertree.Signing.Prelude
