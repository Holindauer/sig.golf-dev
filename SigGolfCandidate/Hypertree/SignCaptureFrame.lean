import SigGolfCandidate.Hypertree.SignChainStep

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def CapturePointerValid (pointer : Nat) : Prop :=
  0x20060 ≤ pointer ∧ pointer + 752 ≤ 0x40000 ∧ pointer % 8 = 0

theorem capture_target (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    s.getMem 0x80448 + (s.getMem 0x80430 <<< 4) = BitVec.ofNat 64 (pointer + 16 * chain.val) := by
  rw [ptr, chn]
  apply BitVec.eq_of_toNat_eq
  have bound := chain.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem capture_target_next (pointer : Nat) (chain : Reference.Chain) :
    BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 =
      BitVec.ofNat 64 (pointer + 16 * chain.val + 8) := (BitVec.ofNat_add _ _).symm

theorem capture_access (pointer : Nat) (chain : Reference.Chain) (valid : CapturePointerValid pointer) :
    accessValid (BitVec.ofNat 64 (pointer + 16 * chain.val)) 8 = true ∧
    accessValid (BitVec.ofNat 64 (pointer + 16 * chain.val + 8)) 8 = true := by
  have bound := chain.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp [accessValid, rangeValid, MEMORY_BYTES]
  omega

theorem capture_digit_access (s : MachineState) (chain : Reference.Chain)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    accessValid (0x80600 + s.getMem 0x80430) 1 = true := by
  rw [chn]
  have bound := chain.isLt
  simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_add]
  omega

theorem captureUpper_frame (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (a : Word) (outside : ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) :
    (captureUpperState s).getMem a = s.getMem a := by
  rw [captureUpper_mem, capture_target s pointer chain valid ptr chn, capture_target_next]
  have zero : a ≠ BitVec.ofNat 64 (pointer + 16 * chain.val) := outside 0
  have one : a ≠ BitVec.ofNat 64 (pointer + 16 * chain.val + 8) := outside 1
  simp only [if_neg zero, if_neg one, ite_self]

theorem captureUpper_high_frame (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (a : Word) (high : 0x80000 ≤ a.toNat) :
    (captureUpperState s).getMem a = s.getMem a := by
  apply captureUpper_frame s pointer chain valid ptr chn a
  intro i eq
  have bound := chain.isLt
  have ibound := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem captureUpper_ra (s : MachineState) :
    (captureUpperState s).getReg .x1 = s.getReg .x1 := by
  unfold captureUpperState
  split
  · simp [captureModeState, execInstrBr, MachineState.getReg_setReg_ne]
  · split
    · unfold captureUpperTailState
      split <;> simp [captureUpperPrepared, captureWriteState, capturePositionState,
        captureDigitState, capturePointerState, captureSelectorState, captureModeState,
        execInstrBr, MachineState.getReg_setReg_ne]
    · simp [captureSelectorState, captureModeState, execInstrBr, MachineState.getReg_setReg_ne]

theorem captureUpper_chainData (s : MachineState) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain step value) :
    ChainData (captureUpperState s) level tree side chain step value := by
  have keep := captureUpper_high_frame s pointer chain valid ptr data.chainEq
  constructor
  · rw [keep _ (by decide)]; exact data.levelEq
  · rw [keep _ (by decide)]; exact data.leafEq
  · rw [keep _ (by decide)]; exact data.chainEq
  · rw [keep _ (by decide)]; exact data.stepEq
  · intro i; rw [keep _ (by fin_cases i <;> decide)]; exact data.indexEq i
  · intro i; rw [keep _ (by fin_cases i <;> decide)]; exact data.valueEq i

end SigGolfCandidate.Hypertree.Signing
