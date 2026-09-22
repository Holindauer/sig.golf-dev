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

/-- Every loaded word is the corresponding little-endian chunk, padded with zeros. -/
theorem write_word (s : MachineState) (base : Nat) (bs : List Byte) (i : Nat)
    (bound : base + 8 * ((bs.length + 7) / 8) < 2 ^ 64)
    (hi : 8 * i < bs.length) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bs).getMem (BitVec.ofNat 64 (base + 8 * i)) =
      packBytes ((bs.drop (8 * i)).take 8) := by
  induction i generalizing s base bs with
  | zero =>
    cases bs with
    | nil => simp at hi
    | cons b bs =>
      rw [MachineState.writeBytesAsWords]
      have next : BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base + 8) := (BitVec.ofNat_add _ _).symm
      simp only [Nat.mul_zero, Nat.add_zero, List.drop_zero]
      rw [next, write_preserves]
      · rw [MachineState.getMem_setMem_eq, bytesToWordLE_eq_packBytes]
      · simp only [List.length_drop, List.length_cons]
        simp only [List.length_cons] at bound
        omega
      · left
        have small : base < 2 ^ 64 := by omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        omega
  | succ i ih =>
    cases bs with
    | nil => simp at hi
    | cons b bs =>
      rw [MachineState.writeBytesAsWords]
      have next : BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base + 8) := (BitVec.ofNat_add _ _).symm
      rw [next]
      have offset : base + 8 * (i + 1) = base + 8 + 8 * i := by omega
      rw [offset, ih]
      · simp only [List.drop_drop]
        rw [show 8 + 8 * i = 8 * (i + 1) by omega]
      · simp only [List.length_drop, List.length_cons]
        simp only [List.length_cons] at bound
        omega
      · simp only [List.length_drop, List.length_cons]
        simp only [List.length_cons] at hi
        omega

/-- Reading any byte within a loaded buffer returns that exact input byte. -/
theorem write_byte (s : MachineState) (base : Nat) (bs : List Byte) (i : Nat)
    (aligned : base % 8 = 0)
    (bound : base + 8 * ((bs.length + 7) / 8) < 2 ^ 64)
    (hi : i < bs.length) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bs).getByte (BitVec.ofNat 64 (base + i)) = bs[i] := by
  have small : base < 2 ^ 64 := by omega
  have halign : (BitVec.ofNat 64 base).toNat % 8 = 0 := by simpa [Nat.mod_eq_of_lt small] using aligned
  have hover : (BitVec.ofNat 64 base).toNat + i < 2 ^ 64 := by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]; omega
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover]
  rw [← BitVec.ofNat_add, write_word s base bs (i / 8) bound (by omega)]
  rw [extractByte_packBytes _ _ (by omega) (by rw [List.length_take, List.length_drop]; omega),
    List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- Reassembling the first n base-2^width digits recovers exactly that prefix. -/
theorem digit_fold (x width n initial : Nat) :
    (List.range n).foldl (fun acc i => acc + (x / 2 ^ (width * i) % 2 ^ width) * 2 ^ (width * i)) initial =
      initial + x % 2 ^ (width * n) := by
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.add_zero]
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    ac_rfl

theorem foldl_eq_on {α β : Type} (xs : List α) (f g : β → α → β)
    (same : ∀ x, x ∈ xs → ∀ acc, f acc x = g acc x) (acc : β) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (by simp)]
    exact ih (fun y hy => same y (by simp [hy])) _

/-- The official output decoder inverts the byte encoding. -/
theorem readBuffer_of_bytes (s : MachineState) (base n : Nat) (value : Bytes n)
    (h : ∀ i, i < n → s.getByte (BitVec.ofNat 64 (base + i)) = value.extractLsb' (8 * i) 8) :
    readBuffer s base n = value := by
  unfold readBuffer
  have same : (List.range n).foldl (fun acc i => acc + (s.getByte (BitVec.ofNat 64 (base + i))).toNat * 2 ^ (8 * i)) 0 =
      (List.range n).foldl (fun acc i => acc + (value.toNat / 2 ^ (8 * i) % 2 ^ 8) * 2 ^ (8 * i)) 0 := by
    apply foldl_eq_on
    intro i hi acc
    rw [h i (by simpa using hi), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [same, digit_fold]
  simp

/-- Loading and decoding a fixed-size value is an exact round trip. -/
theorem read_write_buffer (s : MachineState) (base n : Nat) (value : Bytes n)
    (aligned : base % 8 = 0) (bound : base + 8 * ((n + 7) / 8) < 2 ^ 64) :
    readBuffer (s.writeBytesAsWords (BitVec.ofNat 64 base) (bytes value)) base n = value := by
  apply readBuffer_of_bytes
  intro i hi
  have len : (bytes value).length = n := by simp [bytes]
  rw [write_byte s base (bytes value) i aligned (by simpa [len] using bound) (by simpa [len] using hi)]
  simp [bytes]

theorem getByte_setReg (s : MachineState) (reg : Reg) (v address : Word) :
    (s.setReg reg v).getByte address = s.getByte address := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]

theorem readBuffer_setReg (s : MachineState) (reg : Reg) (v : Word) (base n : Nat) :
    readBuffer (s.setReg reg v) base n = readBuffer s base n := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem_setReg]

/-- A disjoint write preserves bytes of an aligned neighboring buffer. -/
theorem write_preserves_byte (s : MachineState) (base : Nat) (bs : List Byte) (readBase i : Nat)
    (aligned : readBase % 8 = 0)
    (writeBound : base + 8 * ((bs.length + 7) / 8) < 2 ^ 64)
    (readBound : readBase + i < 2 ^ 64)
    (outside : readBase + i < base ∨ base + 8 * ((bs.length + 7) / 8) ≤ readBase) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bs).getByte (BitVec.ofNat 64 (readBase + i)) =
      s.getByte (BitVec.ofNat 64 (readBase + i)) := by
  have small : readBase < 2 ^ 64 := by omega
  have ha : (BitVec.ofNat 64 readBase).toNat % 8 = 0 := by simpa [Nat.mod_eq_of_lt small] using aligned
  have hb : (BitVec.ofNat 64 readBase).toNat + i < 2 ^ 64 := by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using readBound
  simp only [MachineState.getByte, BitVec.ofNat_add, alignToDword_add_ofNat_of_aligned ha hb]
  apply congrArg (fun word => extractByte word _)
  apply write_preserves _ _ _ _ writeBound
  rw [← BitVec.ofNat_add]
  have wordBound : readBase + 8 * (i / 8) < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
  omega

@[simp] theorem bytes_length {n : Nat} (value : Bytes n) : (bytes value).length = n := by simp [bytes]

/-- A loaded typed value has exactly its declared byte representation. -/
theorem write_value_byte (s : MachineState) (base n : Nat) (value : Bytes n) (i : Nat)
    (aligned : base % 8 = 0) (bound : base + 8 * ((n + 7) / 8) < 2 ^ 64) (hi : i < n) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) (bytes value)).getByte (BitVec.ofNat 64 (base + i)) =
      value.extractLsb' (8 * i) 8 := by
  rw [write_byte s base (bytes value) i aligned (by simpa using bound) (by simpa using hi)]
  simp [bytes]

/-- info: 'SigGolfCandidate.Memory.write_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write_word

/-- info: 'SigGolfCandidate.Memory.read_write_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_write_buffer

end SigGolfCandidate.Memory
