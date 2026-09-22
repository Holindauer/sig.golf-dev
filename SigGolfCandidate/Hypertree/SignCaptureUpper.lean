import SigGolfCandidate.Hypertree.SignCaptureRun

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def CaptureDigitMatches (s : MachineState) : Prop :=
  (s.getByte (0x80600 + s.getMem 0x80430)).zeroExtend 64 = s.getMem 0x80438
instance (s : MachineState) : Decidable (CaptureDigitMatches s) := inferInstanceAs (Decidable (_ = _))

structure UpperCaptureTailCode (image : Image) (base : Word) : Prop where
  digit : captureDigitCode image base
  position : capturePositionCode image (base + 44)
  write : captureWriteCode image (base + 52)

def captureUpperTailState (s : MachineState) : MachineState :=
  let d := captureDigitState s
  if CaptureDigitMatches s then captureWriteState (capturePositionState d) else d

theorem captureUpperTail_block (image : Image) (base : Word) (code : UpperCaptureTailCode image base)
    (s : MachineState) (pc : s.pc = base)
    (digitSafe : accessValid (0x80600 + s.getMem 0x80430) 1 = true)
    (safe : accessValid (s.getReg .x7 + (s.getMem 0x80430 <<< 4)) 8 = true)
    (safeNext : accessValid (s.getReg .x7 + (s.getMem 0x80430 <<< 4) + 8) 8 = true) :
    OrdinarySteps image s (if CaptureDigitMatches s then 21 else 11) (captureUpperTailState s) := by
  have digit := captureDigit_block image base code.digit s pc digitSafe
  unfold captureUpperTailState
  split
  · rename_i matching
    unfold CaptureDigitMatches at matching
    have digitpc : (captureDigitState s).pc = base + 44 := by
      rw [captureDigit_pc, if_pos matching, pc]
    have position := capturePosition_block image (base + 44) code.position _ digitpc
    have positionpc : (capturePositionState (captureDigitState s)).pc = base + 52 := by
      rw [capturePosition_pc, digitpc]
      simp [BitVec.add_assoc]
    have write := captureWrite_block image (base + 52) code.write _ positionpc
      (by simpa only [capturePosition_reg, captureDigit_regs] using safe)
      (by simpa only [capturePosition_reg, captureDigit_regs] using safeNext)
    exact Keygen.ordinary_trans image s _ _ 11 10 digit
      (Keygen.ordinary_trans image _ _ _ 2 8 position write)
  · exact digit

theorem captureUpperTail_pc (s : MachineState) : (captureUpperTailState s).pc = s.pc + 84 := by
  unfold captureUpperTailState
  split
  · rename_i matching
    unfold CaptureDigitMatches at matching
    rw [captureWrite_pc, capturePosition_pc, captureDigit_pc, if_pos matching]
    simp [BitVec.add_assoc]
  · rename_i unmatched
    unfold CaptureDigitMatches at unmatched
    rw [captureDigit_pc, if_neg unmatched]

theorem captureUpperTail_mem (s : MachineState) (a : Word) :
    (captureUpperTailState s).getMem a = if CaptureDigitMatches s then
      if a = s.getReg .x7 + (s.getMem 0x80430 <<< 4) + 8 then s.getMem 0x80518 else
      if a = s.getReg .x7 + (s.getMem 0x80430 <<< 4) then s.getMem 0x80510 else s.getMem a
    else s.getMem a := by
  unfold captureUpperTailState
  split <;> simp only [captureWrite_mem, capturePosition_reg, captureDigit_regs,
    capturePosition_mem, captureDigit_mem]

theorem captureUpperTail_sp (s : MachineState) :
    (captureUpperTailState s).getReg .x2 = s.getReg .x2 := by
  unfold captureUpperTailState
  split <;> simp only [captureWrite_sp, capturePosition_sp, captureDigit_sp]

structure UpperCaptureCode (image : Image) (base : Word) : Prop where
  mode : captureModeCode image base 128
  selector : captureSelectorCode image (base + 16) 100
  pointer : capturePointerCode image (base + 44)
  tail : UpperCaptureTailCode image (base + 56)

def captureUpperPrepared (s : MachineState) : MachineState :=
  capturePointerState (captureSelectorState 100 (captureModeState 128 s))

theorem captureUpperPrepared_mem (s : MachineState) (a : Word) :
    (captureUpperPrepared s).getMem a = s.getMem a := by
  simp only [captureUpperPrepared, capturePointer_mem, captureSelector_mem, captureMode_mem]

theorem captureUpperPrepared_reg (s : MachineState) :
    (captureUpperPrepared s).getReg .x7 = s.getMem 0x80448 := by
  simp only [captureUpperPrepared, capturePointer_reg, captureSelector_mem, captureMode_mem]

theorem captureUpperPrepared_sp (s : MachineState) :
    (captureUpperPrepared s).getReg .x2 = s.getReg .x2 := by
  simp only [captureUpperPrepared, capturePointer_sp, captureSelector_sp, captureMode_sp]

theorem captureUpperPrepared_matches (s : MachineState) :
    CaptureDigitMatches (captureUpperPrepared s) ↔ CaptureDigitMatches s := by
  simp only [CaptureDigitMatches, MachineState.getByte, captureUpperPrepared_mem]

def captureUpperState (s : MachineState) : MachineState :=
  let m := captureModeState 128 s
  if s.getMem 0x80440 = 0 then m else
  if s.getMem 0x80428 = s.getMem 0x80420 then captureUpperTailState (captureUpperPrepared s)
  else captureSelectorState 100 m

def captureUpperSteps (s : MachineState) : Nat :=
  if s.getMem 0x80440 = 0 then 4 else
  if s.getMem 0x80428 = s.getMem 0x80420 then
    if CaptureDigitMatches s then 35 else 25
  else 11

theorem captureUpper_block (image : Image) (base : Word) (code : UpperCaptureCode image base)
    (s : MachineState) (pc : s.pc = base)
    (digitSafe : accessValid (0x80600 + s.getMem 0x80430) 1 = true)
    (safe : accessValid (s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)) 8 = true)
    (safeNext : accessValid (s.getMem 0x80448 + (s.getMem 0x80430 <<< 4) + 8) 8 = true) :
    OrdinarySteps image s (captureUpperSteps s) (captureUpperState s) := by
  have mode := captureMode_block image base 128 code.mode s pc
  unfold captureUpperState captureUpperSteps
  split
  · exact mode
  · rename_i enabled
    have modepc : (captureModeState 128 s).pc = base + 16 := by
      rw [captureMode_pc, if_neg enabled, pc]
    have selector := captureSelector_block image (base + 16) 100 code.selector _ modepc
    split
    · rename_i selected
      have selected' : (captureModeState 128 s).getMem 0x80428 =
          (captureModeState 128 s).getMem 0x80420 := by simpa only [captureMode_mem] using selected
      have selectorpc : (captureSelectorState 100 (captureModeState 128 s)).pc = base + 44 := by
        rw [captureSelector_pc, if_pos selected', modepc]
        simp [BitVec.add_assoc]
      have pointer := capturePointer_block image (base + 44) code.pointer _ selectorpc
      have preparedpc : (captureUpperPrepared s).pc = base + 56 := by
        rw [captureUpperPrepared, capturePointer_pc, selectorpc]
        simp [BitVec.add_assoc]
      have tail := captureUpperTail_block image (base + 56) code.tail _ preparedpc
        (by simpa only [captureUpperPrepared_mem] using digitSafe)
        (by simpa only [captureUpperPrepared_reg, captureUpperPrepared_mem] using safe)
        (by simpa only [captureUpperPrepared_reg, captureUpperPrepared_mem] using safeNext)
      have all := Keygen.ordinary_trans image s _ _ 4 _ mode
        (Keygen.ordinary_trans image _ _ _ 7 _ selector
          (Keygen.ordinary_trans image _ _ _ 3 _ pointer tail))
      simp only [captureUpperPrepared_matches] at all
      split <;> simp_all only [if_true, if_false]
    · exact Keygen.ordinary_trans image s _ _ 4 7 mode selector

theorem captureUpper_pc (s : MachineState) : (captureUpperState s).pc = s.pc + 140 := by
  unfold captureUpperState
  split
  · rename_i disabled
    rw [captureMode_pc, if_pos disabled]
    simp [signExtend13, BitVec.add_assoc]
  · rename_i enabled
    have modepc : (captureModeState 128 s).pc = s.pc + 16 := by rw [captureMode_pc, if_neg enabled]
    split
    · rename_i selected
      rw [captureUpperTail_pc, captureUpperPrepared, capturePointer_pc, captureSelector_pc]
      simp only [captureMode_mem, selected, if_true, modepc]
      simp [BitVec.add_assoc]
    · rename_i unselected
      rw [captureSelector_pc]
      simp only [captureMode_mem, unselected, if_false, modepc]
      simp [signExtend13, BitVec.add_assoc]

theorem captureUpper_mem (s : MachineState) (a : Word) :
    (captureUpperState s).getMem a =
      if s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 ∧ CaptureDigitMatches s then
        if a = s.getMem 0x80448 + (s.getMem 0x80430 <<< 4) + 8 then s.getMem 0x80518 else
        if a = s.getMem 0x80448 + (s.getMem 0x80430 <<< 4) then s.getMem 0x80510 else s.getMem a
      else s.getMem a := by
  unfold captureUpperState
  split
  · rename_i disabled
    simp only [captureMode_mem, disabled, ne_eq, not_true_eq_false, false_and, if_false]
  · rename_i enabled
    split <;> simp_all only [captureUpperTail_mem, captureUpperPrepared_reg, captureUpperPrepared_mem,
      captureUpperPrepared_matches, captureSelector_mem, captureMode_mem, ne_eq,
      not_false_eq_true, true_and, false_and, if_true, if_false]

theorem captureUpper_sp (s : MachineState) :
    (captureUpperState s).getReg .x2 = s.getReg .x2 := by
  unfold captureUpperState
  split
  · exact captureMode_sp _ _
  · split <;> simp only [captureUpperTail_sp, captureUpperPrepared_sp, captureSelector_sp, captureMode_sp]

theorem captureUpper_steps_le (s : MachineState) : captureUpperSteps s ≤ 35 := by
  unfold captureUpperSteps
  split <;> (try split) <;> (try split) <;> decide

theorem sign_upper_capture_code : UpperCaptureCode sign 0x1698 :=
  ⟨sign_upper_mode_code, sign_upper_selector_code, sign_upper_pointer_code,
    ⟨sign_upper_digit_code, sign_upper_position_code, sign_upper_write_code⟩⟩

theorem keygen_upper_capture_code : UpperCaptureCode keygen 0x1318 :=
  ⟨keygen_upper_mode_code, keygen_upper_selector_code, keygen_upper_pointer_code,
    ⟨keygen_upper_digit_code, keygen_upper_position_code, keygen_upper_write_code⟩⟩

end SigGolfCandidate.Hypertree.Signing
