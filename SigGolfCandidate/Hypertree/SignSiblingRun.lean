import SigGolfCandidate.Hypertree.SignSibling

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def siblingPrepared (s : MachineState) : MachineState := siblingPointerState (siblingReadState s)
def siblingSource (s : MachineState) : Word := 0x80520 + ((s.getMem 0x80420 ^^^ 1) <<< 4)
def siblingDestination (s : MachineState) : Word :=
  s.getMem 0x80448 + (if s.getMem 0x80400 = 0 then 16 else 736)

theorem siblingPrepared_block (image : Image) (base : Word) (code : SiblingPrepareCode image base)
    (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s (if s.getMem 0x80400 = 0 then 16 else 17) (siblingPrepared s) := by
  have read := siblingRead_block image base code s (by simpa using pc)
  have readpc : (siblingReadState s).pc = base + 56 := by rw [siblingRead_pc, pc]
  have pointer := siblingPointerState_block image base code _ readpc
  have all := Keygen.ordinary_trans image s _ _ 14 _ read pointer
  rw [(siblingRead_regs s).2.2] at all
  have count : (if s.getMem 0x80400 = 0 then 2 else 3) + 14 =
      (if s.getMem 0x80400 = 0 then 16 else 17) := by split <;> rfl
  rw [count] at all
  exact all

theorem siblingPrepared_pc (s : MachineState) (base : Word) (pc : s.pc = base) :
    (siblingPrepared s).pc = base + 72 := by
  apply siblingPointer_pc
  rw [siblingRead_pc, pc]

theorem siblingPrepared_regs (s : MachineState) :
    (siblingPrepared s).getReg .x7 = siblingSource s ∧
    (siblingPrepared s).getReg .x10 = siblingDestination s := by
  simp only [siblingPrepared, siblingPointer_regs, siblingRead_regs, siblingSource, siblingDestination,
    and_self]

theorem siblingPrepared_mem (s : MachineState) (a : Word) :
    (siblingPrepared s).getMem a = s.getMem a := by
  simp only [siblingPrepared, siblingPointer_mem, siblingRead_mem]

theorem siblingPrepared_sp (s : MachineState) :
    (siblingPrepared s).getReg .x2 = s.getReg .x2 := by
  simp only [siblingPrepared, siblingPointer_sp, siblingRead_sp]

def siblingState (s : MachineState) : MachineState := siblingCopyState (siblingPrepared s)

theorem sibling_block (image : Image) (base : Word) (code : SiblingCode image base)
    (s : MachineState) (pc : s.pc = base)
    (src : accessValid (siblingSource s) 8 = true)
    (srcNext : accessValid (siblingSource s + 8) 8 = true)
    (dst : accessValid (siblingDestination s) 8 = true)
    (dstNext : accessValid (siblingDestination s + 8) 8 = true) :
    OrdinarySteps image s (if s.getMem 0x80400 = 0 then 20 else 21) (siblingState s) := by
  have prepare := siblingPrepared_block image base code.prepare s pc
  have copy := siblingCopy_block image base code.copy _ (siblingPrepared_pc s base pc)
    (by simpa only [siblingPrepared_regs] using src)
    (by simpa only [siblingPrepared_regs] using srcNext)
    (by simpa only [siblingPrepared_regs] using dst)
    (by simpa only [siblingPrepared_regs] using dstNext)
  have all := Keygen.ordinary_trans image s _ _ _ 4 prepare copy
  have count : 4 + (if s.getMem 0x80400 = 0 then 16 else 17) =
      (if s.getMem 0x80400 = 0 then 20 else 21) := by split <;> rfl
  rw [count] at all
  exact all

theorem siblingState_pc (s : MachineState) (base : Word) (pc : s.pc = base) :
    (siblingState s).pc = base + 88 := by
  rw [siblingState, siblingCopy_pc, siblingPrepared_pc s base pc]
  simp [BitVec.add_assoc]

theorem siblingState_mem (s : MachineState) (a : Word) :
    (siblingState s).getMem a = if a = siblingDestination s + 8 then s.getMem (siblingSource s + 8) else
      if a = siblingDestination s then s.getMem (siblingSource s) else s.getMem a := by
  simp only [siblingState, siblingCopy_mem, siblingPrepared_regs, siblingPrepared_mem]

theorem siblingState_sp (s : MachineState) :
    (siblingState s).getReg .x2 = s.getReg .x2 := by
  simp only [siblingState, siblingCopy_sp, siblingPrepared_sp]

theorem sign_sibling_prepare_code : SiblingPrepareCode sign 0x1408 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem verify_sibling_prepare_code : SiblingPrepareCode verify 0x1314 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_sibling_code : SiblingCode sign 0x1408 := by
  refine ⟨sign_sibling_prepare_code, ?_⟩
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem sign_sibling_mode_code : captureModeCode sign 0x13f8 92 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_sibling_prepare_code : SiblingPrepareCode keygen 0x1088 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_sibling_code : SiblingCode keygen 0x1088 := by
  refine ⟨keygen_sibling_prepare_code, ?_⟩
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem keygen_sibling_mode_code : captureModeCode keygen 0x1078 92 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.Signing
