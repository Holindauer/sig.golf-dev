import SigGolfCandidate.Hypertree.SignBottomHash

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def OutsideBottomWork (side : Bool) (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) ∧
  ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val

theorem low_outside_bottom (side : Bool) (a : Word) (low : a.toNat < 0x80000) : OutsideBottomWork side a := by
  unfold OutsideBottomWork
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i eq
  all_goals have h := congrArg BitVec.toNat eq
  all_goals have ib := i.isLt
  all_goals cases side <;> simp [wordAddress, KeygenSavePublic.wordAddress, Reference.sideNumber] at h <;> omega

theorem captureBottom_frame (s : MachineState) (pointer : Nat)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (a : Word)
    (outside : ∀ i : Fin 2, a ≠ wordAddress pointer i.val) :
    (captureBottomState s).getMem a = s.getMem a := by
  rw [captureBottom_mem, ptr]
  have zero : a ≠ BitVec.ofNat 64 pointer := outside 0
  have one : a ≠ BitVec.ofNat 64 pointer + 8 := by
    have h := outside 1
    simpa [wordAddress, BitVec.ofNat_add] using h
  simp only [if_neg zero, if_neg one, ite_self]

theorem captureBottom_high_frame (s : MachineState) (pointer : Nat) (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (a : Word) (high : 0x80000 ≤ a.toNat) :
    (captureBottomState s).getMem a = s.getMem a := by
  apply captureBottom_frame s pointer ptr a
  intro i eq
  rcases valid with ⟨lower, upper, aligned⟩
  have ib := i.isLt
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem captureBottom_ra (s : MachineState) :
    (captureBottomState s).getReg .x1 = s.getReg .x1 := by
  unfold captureBottomState
  split
  · simp [captureModeState, execInstrBr, MachineState.getReg_setReg_ne]
  · split <;> simp [captureWriteState, capturePointerState, captureSelectorState, captureModeState,
      execInstrBr, MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.Signing
