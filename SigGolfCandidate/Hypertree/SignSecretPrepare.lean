import SigGolfCandidate.Hypertree.SignSites
import SigGolfCandidate.Hypertree.KeygenStepZero

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Metadata and secret key needed at the start of each signer upper-leaf chain. -/
structure LeafData (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Nat) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyEq : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64

/-- Secret derivation and actual STEP reset initialize the complete signer chain loop. -/
theorem sign_secret_prepare (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (data : LeafData s secretKey level tree side chain.val) :
    ∃ final, Trace hash sign s 93 100 1 1 final ∧ final.pc = 0x1698 ∧
      ChainData final level tree side chain 0 (Reference.secret hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨secret, pre, secretPC, secretWords, ra, sp, frame⟩ := KeygenSecret.compute sign hash 0x1584 sign_upper_secret_code
    s pc level tree side chain secretKey data.levelEq data.leafEq data.chainEq data.indexEq data.secretKeyEq
  have reset := KeygenStepZero.block sign 0x1688 KeygenStepZero.sign_code secret secretPC
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
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
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
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
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

end SigGolfCandidate.Hypertree.Signing
