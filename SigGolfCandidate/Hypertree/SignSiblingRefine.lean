import SigGolfCandidate.Hypertree.SignTreeStart

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem sibling_source_eq (s : MachineState) (selected : Bool)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)) :
    siblingSource s = KeygenSavePublic.wordAddress (!selected) 0 ∧
      siblingSource s + 8 = KeygenSavePublic.wordAddress (!selected) 1 := by
  unfold siblingSource
  rw [selector]
  cases selected <;> constructor <;> rfl

theorem sibling_upper_destination (s : MachineState) (pointer : Nat)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (nonzero : s.getMem 0x80400 ≠ 0) :
    siblingDestination s = BitVec.ofNat 64 (pointer + 736) := by
  rw [siblingDestination, if_neg nonzero, ptr]
  exact (BitVec.ofNat_add _ _).symm

theorem sibling_upper_safe (pointer : Nat) (valid : CapturePointerValid pointer) :
    accessValid (BitVec.ofNat 64 (pointer + 736)) 8 = true ∧
    accessValid (BitVec.ofNat 64 (pointer + 736) + 8) 8 = true := by
  rcases valid with ⟨lower, upper, aligned⟩
  simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_add]
  omega

def SiblingStored (s : MachineState) (pointer : Nat) (value : Reference.Digest) : Prop :=
  ∀ i : Fin 2, s.getMem (wordAddress (pointer + 736) i.val) = value.extractLsb' (64*i.val) 64

/-- The actual enabled upper-layer sibling path copies the opposite public leaf root to
the authentication-node slot. All other words, including the signature vector, are framed. -/
theorem sign_upper_sibling (s : MachineState) (pointer : Nat) (selected : Bool) (value : Reference.Digest)
    (pc : s.pc = 0x13f8) (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (enabled : s.getMem 0x80440 ≠ 0)
    (nonzero : s.getMem 0x80400 ≠ 0)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected))
    (words : ∀ i : Fin 2, s.getMem (KeygenSavePublic.wordAddress (!selected) i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps sign s 25 final ∧ final.pc = 0x1460 ∧
      SiblingStored final pointer value ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress (pointer + 736) i.val) → final.getMem a = s.getMem a) := by
  let ready := captureModeState 92 s
  have mode := captureMode_block sign 0x13f8 92 sign_sibling_mode_code s pc
  have readyPC : ready.pc = 0x1408 := by rw [captureMode_pc, if_neg enabled, pc]; rfl
  have readyNonzero : ready.getMem 0x80400 ≠ 0 := by simpa only [ready, captureMode_mem] using nonzero
  have readyPointer : ready.getMem 0x80448 = BitVec.ofNat 64 pointer := by simpa only [ready, captureMode_mem] using ptr
  have readySelector : ready.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected) := by simpa only [ready, captureMode_mem] using selector
  have source := sibling_source_eq ready selected readySelector
  have destination := sibling_upper_destination ready pointer readyPointer readyNonzero
  have safe := sibling_upper_safe pointer valid
  have copy := sibling_block sign 0x1408 sign_sibling_code ready readyPC
    (by rw [source.1]; cases selected <;> decide)
    (by rw [source.2]; cases selected <;> decide)
    (by rw [destination]; exact safe.1) (by rw [destination]; exact safe.2)
  rw [if_neg readyNonzero] at copy
  refine ⟨siblingState ready, ordinary_trans sign s ready _ 4 21 mode copy,
    siblingState_pc ready 0x1408 readyPC, ?_, (siblingState_sp ready).trans (captureMode_sp 92 s), ?_⟩
  · intro i
    rw [siblingState_mem, destination, source.2, source.1]
    have next : wordAddress (pointer+736) 1 = BitVec.ofNat 64 (pointer+736) + 8 := BitVec.ofNat_add _ _
    have ne : BitVec.ofNat 64 (pointer+736) ≠ BitVec.ofNat 64 (pointer+736) + 8 := by
      intro eq
      have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
      contradiction
    fin_cases i
    · change (if BitVec.ofNat 64 (pointer+736) = BitVec.ofNat 64 (pointer+736) + 8 then _ else _) = _
      rw [if_neg ne]
      simpa [wordAddress, ready, captureMode_mem] using words 0
    · rw [next, if_pos rfl, captureMode_mem]
      exact words 1
  · intro a outside
    rw [siblingState_mem, destination, source.2, source.1]
    have zero : a ≠ BitVec.ofNat 64 (pointer+736) := outside 0
    have one : a ≠ BitVec.ofNat 64 (pointer+736) + 8 := by simpa [wordAddress, BitVec.ofNat_add] using outside 1
    rw [if_neg one, if_neg zero, captureMode_mem]

end SigGolfCandidate.Hypertree.Signing
