import SigGolfCandidate.Hypertree.SignChainLoop

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

structure CaptureSettings (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selected : s.getMem 0x80428 = s.getMem 0x80420
  digitEq : s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) = BitVec.ofNat 8 digit.val

def CapturedValue (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (value : Reference.Digest) : Prop :=
  ∀ i : Fin 2, s.getMem (wordAddress (pointer + 16 * chain.val) i.val) = value.extractLsb' (64 * i.val) 64

theorem capture_matches_iff (s : MachineState) (pointer step : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (settings : CaptureSettings s pointer chain digit) (bound : step ≤ 7)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (stp : s.getMem 0x80438 = BitVec.ofNat 64 step) :
    CaptureDigitMatches s ↔ step = digit.val := by
  unfold CaptureDigitMatches
  rw [chn, show (0x80600 : Word) + BitVec.ofNat 64 chain.val = BitVec.ofNat 64 (0x80600 + chain.val)
    from (BitVec.ofNat_add _ _).symm, settings.digitEq, stp]
  rw [BitVec.toNat_eq]
  have dbound := digit.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem capture_selected_value (s : MachineState) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (data : ChainData s level tree side chain step value) (bound : step ≤ 7)
    (matching : step = digit.val) : CapturedValue (captureUpperState s) pointer chain value := by
  have test := (capture_matches_iff s pointer step chain digit settings bound data.chainEq data.stepEq).2 matching
  have condition : s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 ∧ CaptureDigitMatches s :=
    ⟨settings.enabled, settings.selected, test⟩
  intro i
  rw [captureUpper_mem, if_pos condition,
    capture_target s pointer chain valid settings.pointerEq data.chainEq]
  have ne : BitVec.ofNat 64 (pointer + 16 * chain.val) ≠ BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 := by
    intro eq
    have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
    contradiction
  fin_cases i
  · change (if BitVec.ofNat 64 (pointer + 16 * chain.val) = BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 then _ else _) = _
    rw [if_neg ne]
    simpa [wordAddress] using data.valueEq 0
  · have address : wordAddress (pointer + 16 * chain.val) 1 = BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 :=
      BitVec.ofNat_add _ _
    rw [address, if_pos rfl]
    exact data.valueEq 1

theorem capture_selected_keep (s : MachineState) (pointer step : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (settings : CaptureSettings s pointer chain digit) (bound : step ≤ 7)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (stp : s.getMem 0x80438 = BitVec.ofNat 64 step) (different : step ≠ digit.val) (a : Word) :
    (captureUpperState s).getMem a = s.getMem a := by
  rw [captureUpper_mem]
  have test : ¬ CaptureDigitMatches s := by
    rw [capture_matches_iff s pointer step chain digit settings bound chn stp]
    exact different
  simp only [test, and_false, if_false]

/-- Settings live outside both the hash workspace and this chain's output pair. -/
theorem CaptureSettings.frame (s final : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (frame : ∀ a, OutsideChainWork a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :
    CaptureSettings final pointer chain digit := by
  have outside (a : Word) (high : 0x80000 ≤ a.toNat) :
      ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val := by
    intro i eq
    have bound := chain.isLt
    have ibound := i.isLt
    rcases valid with ⟨lower, upper, aligned⟩
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress, BitVec.toNat_ofNat] at h
    omega
  have keep (a : Word) (work : OutsideChainWork a) (high : 0x80000 ≤ a.toNat) := frame a work (outside a high)
  constructor
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide)]; exact settings.pointerEq
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide)]; exact settings.enabled
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide), keep _ (by unfold OutsideChainWork; decide) (by decide)]
    exact settings.selected
  · rw [getByte_word final 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
      exact settings.digitEq
    · have bound := chain.isLt
      unfold OutsideChainWork
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals (first | intro j eq | intro eq)
      all_goals have h := congrArg BitVec.toNat eq
      all_goals simp [wordAddress] at h
      all_goals omega
    · have bound := chain.isLt
      simp only [wordAddress, BitVec.toNat_ofNat]
      omega

theorem capture_settings (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    CaptureSettings (captureUpperState s) pointer chain digit :=
  settings.frame s (captureUpperState s) pointer chain digit valid
    (fun a _ outside => captureUpper_frame s pointer chain valid settings.pointerEq chn a outside)

theorem capture_output_outside_work (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer) (i : Fin 2) :
    OutsideChainWork (wordAddress (pointer + 16 * chain.val) i.val) := by
  have bound := chain.isLt
  have ibound := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  unfold OutsideChainWork
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (first | intro j eq | intro eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp [wordAddress] at h
  all_goals omega

/-- Immediately after capture, a checkpoint at or before this iteration is stored. -/
theorem capture_completed_checkpoint (s : MachineState) (hash : Hash) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value expected : Reference.Digest)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (data : ChainData s level tree side chain step value) (bound : step ≤ 7)
    (future : step ≤ digit.val → expected = walk (Reference.chainHash hash level tree side chain) step (digit.val - step) value)
    (past : digit.val < step → CapturedValue s pointer chain expected)
    (reached : digit.val ≤ step) : CapturedValue (captureUpperState s) pointer chain expected := by
  by_cases eq : step = digit.val
  · have expectedEq : expected = value := by simpa [eq, walk] using future (by omega)
    rw [expectedEq]
    exact capture_selected_value s pointer level tree step side chain digit value valid settings data bound eq
  · have old := past (by omega)
    intro i
    rw [capture_selected_keep s pointer step chain digit settings bound data.chainEq data.stepEq eq]
    exact old i

end SigGolfCandidate.Hypertree.Signing
