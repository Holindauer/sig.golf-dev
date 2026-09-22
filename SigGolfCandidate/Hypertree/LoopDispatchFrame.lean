import SigGolfCandidate.Hypertree.LoopDispatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

/-- The optional encoder preserves every aligned word outside its digit buffer and saved return address. -/
theorem dispatch_frame_words (s final : MachineState) (stack : s.getReg .x2 = 0x1000000)
    (frame : ∀ a, (∀ i : Fin 46, a ≠ BitVec.ofNat 64 (0x80600+i.val)) →
      final.getByte a = if s.getMem 0x80400 = 0 then s.getByte a else (dispatchSavedState s).getByte a)
    (address : Nat) (aligned : address % 8 = 0) (bound : address+8 < 2^64)
    (separate : address+8 ≤ 0x80600 ∨ 0x80630 ≤ address) (saved : address ≠ 0xfffff0) :
    final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) := by
  have outside (i : Fin 8) (j : Fin 46) :
      BitVec.ofNat 64 (address+i.val) ≠ BitVec.ofNat 64 (0x80600+j.val) := by
    intro eq
    have h := congrArg BitVec.toNat eq
    have hi := i.isLt; have hj := j.isLt
    change (address+i.val) % 2^64 = (0x80600+j.val) % 2^64 at h
    omega
  by_cases bottom : s.getMem 0x80400 = 0
  · apply word_eq_of_bytes s final address aligned bound
    intro i
    rw [frame _ (outside i), if_pos bottom]
  · have words : final.getMem (BitVec.ofNat 64 address) = (dispatchSavedState s).getMem (BitVec.ofNat 64 address) := by
      apply word_eq_of_bytes (dispatchSavedState s) final address aligned bound
      intro i
      rw [frame _ (outside i), if_neg bottom]
    have notStack : BitVec.ofNat 64 address ≠ 0xfffff0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change address % 2^64 = 0xfffff0 at h
      omega
    rw [words, dispatchSavedState, enter_mem, dispatchEncodeState_sp, stack]
    change (if BitVec.ofNat 64 address = 0xfffff0 then _ else _) = _
    rw [if_neg notStack, dispatchEncodeState_mem]

/-- info: 'SigGolfCandidate.Hypertree.Signing.dispatch_frame_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatch_frame_words

end SigGolfCandidate.Hypertree.Signing
