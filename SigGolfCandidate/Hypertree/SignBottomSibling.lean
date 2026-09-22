import SigGolfCandidate.Hypertree.SignBottomTreeLeaves

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem sibling_bottom_destination (s : MachineState) (pointer : Nat)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (zero : s.getMem 0x80400  = 0) :
    siblingDestination s = BitVec.ofNat 64 (pointer + 16) := by
  rw [siblingDestination, if_pos zero, ptr]
  exact (BitVec.ofNat_add _ _).symm

theorem sibling_bottom_safe (pointer : Nat) (valid : CapturePointerValid pointer) :
    accessValid (BitVec.ofNat 64 (pointer + 16)) 8 = true ∧
    accessValid (BitVec.ofNat 64 (pointer + 16) + 8) 8 = true := by
  rcases valid with ⟨lower, bottom, aligned⟩
  simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_add]
  omega

def BottomSiblingStored (s : MachineState) (pointer : Nat) (value : Reference.Digest) : Prop :=
  ∀ i : Fin 2, s.getMem (wordAddress (pointer + 16) i.val) = value.extractLsb' (64*i.val) 64

/-- The actual enabled bottom-layer sibling path copies the opposite public leaf root to
the authentication-node slot. All other words, including the signature vector, are framed. -/
theorem sign_bottom_sibling (s : MachineState) (pointer : Nat) (selected : Bool) (value : Reference.Digest)
    (pc : s.pc = 0x13f8) (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (enabled : s.getMem 0x80440 ≠ 0)
    (zero : s.getMem 0x80400  = 0)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected))
    (words : ∀ i : Fin 2, s.getMem (KeygenSavePublic.wordAddress (!selected) i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps sign s 24 final ∧ final.pc = 0x1460 ∧
      BottomSiblingStored final pointer value ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress (pointer + 16) i.val) → final.getMem a = s.getMem a) := by
  let ready := captureModeState 92 s
  have mode := captureMode_block sign 0x13f8 92 sign_sibling_mode_code s pc
  have readyPC : ready.pc = 0x1408 := by rw [captureMode_pc, if_neg enabled, pc]; rfl
  have readyZero : ready.getMem 0x80400  = 0 := by simpa only [ready, captureMode_mem] using zero
  have readyPointer : ready.getMem 0x80448 = BitVec.ofNat 64 pointer := by simpa only [ready, captureMode_mem] using ptr
  have readySelector : ready.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected) := by simpa only [ready, captureMode_mem] using selector
  have source := sibling_source_eq ready selected readySelector
  have destination := sibling_bottom_destination ready pointer readyPointer readyZero
  have safe := sibling_bottom_safe pointer valid
  have copy := sibling_block sign 0x1408 sign_sibling_code ready readyPC
    (by rw [source.1]; cases selected <;> decide)
    (by rw [source.2]; cases selected <;> decide)
    (by rw [destination]; exact safe.1) (by rw [destination]; exact safe.2)
  rw [if_pos readyZero] at copy
  refine ⟨siblingState ready, ordinary_trans sign s ready _ 4 20 mode copy,
    siblingState_pc ready 0x1408 readyPC, ?_, (siblingState_sp ready).trans (captureMode_sp 92 s), ?_⟩
  · intro i
    rw [siblingState_mem, destination, source.2, source.1]
    have next : wordAddress (pointer+16) 1 = BitVec.ofNat 64 (pointer+16) + 8 := BitVec.ofNat_add _ _
    have ne : BitVec.ofNat 64 (pointer+16) ≠ BitVec.ofNat 64 (pointer+16) + 8 := by
      intro eq
      have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
      contradiction
    fin_cases i
    · change (if BitVec.ofNat 64 (pointer+16) = BitVec.ofNat 64 (pointer+16) + 8 then _ else _) = _
      rw [if_neg ne]
      simpa [wordAddress, ready, captureMode_mem] using words 0
    · rw [next, if_pos rfl, captureMode_mem]
      exact words 1
  · intro a outside
    rw [siblingState_mem, destination, source.2, source.1]
    have zero : a ≠ BitVec.ofNat 64 (pointer+16) := outside 0
    have one : a ≠ BitVec.ofNat 64 (pointer+16) + 8 := by simpa [wordAddress, BitVec.ofNat_add] using outside 1
    rw [if_neg one, if_neg zero, captureMode_mem]

end SigGolfCandidate.Hypertree.Signing
