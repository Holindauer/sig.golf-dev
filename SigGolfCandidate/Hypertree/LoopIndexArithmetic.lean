import SigGolfCandidate.Hypertree.SignShift
import SigGolfCandidate.Hypertree.SignAdvance

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

/-- The actual index-shift block preserves the main stack pointer. -/
theorem shiftIndexState_sp (s : MachineState) :
    (shiftIndexState s).getReg .x2 = s.getReg .x2 := by
  simp [shiftIndexState, execInstrBr, MachineState.getReg_setReg_ne]

theorem shifted_index_nat (index : Nat) (small : index < 2^192) :
    (BitVec.ofNat 192 index >>> 1) = BitVec.ofNat 192 (index/2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem selector_nat (index : Nat) :
    Reference.sideNumber (index % 2 == 1) = index % 2 := by
  have range : index % 2 = 0 ∨ index % 2 = 1 := by omega
  rcases range with h | h <;> simp [Reference.sideNumber, h]

/-- The machine's shifted index and selector match the reference tree coordinates. -/
theorem shift_index_nat (s : MachineState) (index : Nat) (small : index < 2^192)
    (stored : StoredIndex s (BitVec.ofNat 192 index)) :
    StoredIndex (shiftIndexState s) (BitVec.ofNat 192 (index/2)) ∧
      (shiftIndexState s).getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber (index % 2 == 1)) := by
  obtain ⟨next, side⟩ := shiftIndexState_refines s (BitVec.ofNat 192 index) stored
  refine ⟨?_, ?_⟩
  · rw [shifted_index_nat index small] at next
    exact next
  · apply BitVec.eq_of_toNat_eq
    rw [side, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, BitVec.toNat_ofNat, selector_nat]
    omega

theorem level_word_zero (level : Nat) (small : level < 160) :
    BitVec.ofNat 64 level = 0 ↔ level = 0 := by
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    change level % 2^64 = 0 at h
    omega
  · intro eq; rw [eq]; rfl

theorem layer_pointer_aligned (input level : Nat) (aligned : input % 8 = 0) :
    (input+layerOffset level) % 8 = 0 := by
  unfold layerOffset
  split <;> omega

theorem layer_pointer_bound (input level : Nat) (inputBound : input ≤ 0x3d3b0) (small : level < 160) :
    input+layerOffset level+752 ≤ 0x80000 := by
  unfold layerOffset
  split <;> omega

/-- info: 'SigGolfCandidate.Hypertree.Signing.shift_index_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shift_index_nat

end SigGolfCandidate.Hypertree.Signing
