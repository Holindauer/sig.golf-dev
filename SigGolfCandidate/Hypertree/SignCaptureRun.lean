import SigGolfCandidate.Hypertree.SignCapturePrepare

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

structure BottomCaptureCode (image : Image) (base : Word) : Prop where
  mode : captureModeCode image base 76
  selector : captureSelectorCode image (base + 16) 48
  pointer : capturePointerCode image (base + 44)
  write : captureWriteCode image (base + 56)

def captureBottomState (s : MachineState) : MachineState :=
  let m := captureModeState 76 s
  if s.getMem 0x80440 = 0 then m else
  let q := captureSelectorState 48 m
  if s.getMem 0x80428 = s.getMem 0x80420 then
    captureWriteState (capturePointerState q) else q

def captureBottomSteps (s : MachineState) : Nat :=
  if s.getMem 0x80440 = 0 then 4 else
  if s.getMem 0x80428 = s.getMem 0x80420 then 22 else 11

theorem captureBottom_block (image : Image) (base : Word) (code : BottomCaptureCode image base)
    (s : MachineState) (pc : s.pc = base)
    (safe : accessValid (s.getMem 0x80448) 8 = true)
    (safeNext : accessValid (s.getMem 0x80448 + 8) 8 = true) :
    OrdinarySteps image s (captureBottomSteps s) (captureBottomState s) := by
  have mode := captureMode_block image base 76 code.mode s pc
  unfold captureBottomState captureBottomSteps
  split
  · exact mode
  · rename_i enabled
    have modepc : (captureModeState 76 s).pc = base + 16 := by
      rw [captureMode_pc, if_neg enabled, pc]
    have selector := captureSelector_block image (base + 16) 48 code.selector _ modepc
    split
    · rename_i selected
      have selected' : (captureModeState 76 s).getMem 0x80428 =
          (captureModeState 76 s).getMem 0x80420 := by simpa only [captureMode_mem] using selected
      have selectorpc : (captureSelectorState 48 (captureModeState 76 s)).pc = base + 44 := by
        rw [captureSelector_pc, if_pos selected', modepc]
        simp [BitVec.add_assoc]
      have pointer := capturePointer_block image (base + 44) code.pointer _ selectorpc
      have pointerpc : (capturePointerState (captureSelectorState 48 (captureModeState 76 s))).pc = base + 56 := by
        rw [capturePointer_pc, selectorpc]
        simp [BitVec.add_assoc]
      have write := captureWrite_block image (base + 56) code.write _ pointerpc
        (by simpa only [capturePointer_reg, captureSelector_mem, captureMode_mem] using safe)
        (by simpa only [capturePointer_reg, captureSelector_mem, captureMode_mem] using safeNext)
      exact Keygen.ordinary_trans image s _ _ 4 18 mode
        (Keygen.ordinary_trans image _ _ _ 7 11 selector
          (Keygen.ordinary_trans image _ _ _ 3 8 pointer write))
    · exact Keygen.ordinary_trans image s _ _ 4 7 mode selector

theorem captureBottom_pc (s : MachineState) : (captureBottomState s).pc = s.pc + 88 := by
  unfold captureBottomState
  split
  · rename_i disabled
    rw [captureMode_pc, if_pos disabled]
    simp [signExtend13, BitVec.add_assoc]
  · rename_i enabled
    have modepc : (captureModeState 76 s).pc = s.pc + 16 := by rw [captureMode_pc, if_neg enabled]
    split
    · rename_i selected
      rw [captureWrite_pc, capturePointer_pc, captureSelector_pc]
      simp only [captureMode_mem, selected, if_true, modepc]
      simp [BitVec.add_assoc]
    · rename_i unselected
      rw [captureSelector_pc]
      simp only [captureMode_mem, unselected, if_false, modepc]
      simp [signExtend13, BitVec.add_assoc]

theorem captureBottom_mem (s : MachineState) (a : Word) :
    (captureBottomState s).getMem a =
      if s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 then
        if a = s.getMem 0x80448 + 8 then s.getMem 0x80518 else
        if a = s.getMem 0x80448 then s.getMem 0x80510 else s.getMem a
      else s.getMem a := by
  unfold captureBottomState
  split
  · rename_i disabled
    simp only [captureMode_mem, disabled, ne_eq, not_true_eq_false, false_and, if_false]
  · rename_i enabled
    split <;> simp_all only [captureWrite_mem, capturePointer_reg, capturePointer_mem,
      captureSelector_mem, captureMode_mem, ne_eq, not_false_eq_true, true_and, if_true, if_false]

theorem captureBottom_sp (s : MachineState) :
    (captureBottomState s).getReg .x2 = s.getReg .x2 := by
  unfold captureBottomState
  split
  · exact captureMode_sp _ _
  · split <;> simp only [captureWrite_sp, capturePointer_sp, captureSelector_sp, captureMode_sp]

theorem captureBottom_steps_le (s : MachineState) : captureBottomSteps s ≤ 22 := by
  unfold captureBottomSteps
  split <;> (try split) <;> decide

theorem sign_bottom_capture_code : BottomCaptureCode sign 0x1ae0 :=
  ⟨sign_bottom_mode_code, sign_bottom_selector_code, sign_bottom_pointer_code, sign_bottom_write_code⟩

theorem keygen_bottom_capture_code : BottomCaptureCode keygen 0x1760 :=
  ⟨keygen_bottom_mode_code, keygen_bottom_selector_code, keygen_bottom_pointer_code, keygen_bottom_write_code⟩

end SigGolfCandidate.Hypertree.Signing
