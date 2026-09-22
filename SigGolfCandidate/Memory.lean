import SigGolf
import RiscvZkvm.Rv64.Logic.MemRegion

namespace SigGolfCandidate.Memory
open SigGolf RiscvZkvm.Rv64

private theorem getD_eq_byte (bs : List Byte) (i : Nat) : bs[i]?.getD 0 = getByteAt bs i := by
  by_cases h : i < bs.length <;> simp [getByteAt, h]

theorem bytesToWordLE_eq_packBytes (bs : List Byte) : bytesToWordLE bs = packBytes bs := by
  unfold bytesToWordLE packBytes packDword
  simp only [getD_eq_byte]
  rfl

/-- The loader touches only the rounded-up interval occupied by its input buffer. -/
theorem write_preserves (s : MachineState) (base : Nat) (bs : List Byte) (a : Word)
    (bound : base + 8 * ((bs.length + 7) / 8) < 2 ^ 64)
    (outside : a.toNat < base ∨ base + 8 * ((bs.length + 7) / 8) ≤ a.toNat) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bs).getMem a = s.getMem a := by
  cases bs with
  | nil => simp only [MachineState.writeBytesAsWords_nil]
  | cons b bs =>
    rw [MachineState.writeBytesAsWords]
    have next : BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base + 8) := (BitVec.ofNat_add _ _).symm
    rw [next]
    rw [write_preserves _ (base + 8) ((b :: bs).drop 8) a (by simp only [List.length_drop, List.length_cons]; simp only [List.length_cons] at bound; omega) (by simp only [List.length_drop, List.length_cons]; simp only [List.length_cons] at outside; omega)]
    have ne : a ≠ BitVec.ofNat 64 base := by
      intro h
      have same := congrArg BitVec.toNat h
      have small : base < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at same
      simp only [List.length_cons] at outside
      omega
    exact MachineState.getMem_setMem_ne ne
termination_by bs.length
decreasing_by simp_all [List.length_drop]

end SigGolfCandidate.Memory
