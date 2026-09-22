import SigGolfCandidate.Memory
import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Serialization
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- The VM's bit-by-bit hash encoding agrees with the fixed-size byte representation. -/
theorem hashInput_of_bytes (s : MachineState) (base n : Nat) (value : Bytes n)
    (source : s.getReg .x10 = BitVec.ofNat 64 base)
    (bits : (s.getReg .x11).toNat = 8 * n)
    (h : ∀ i, i < n → s.getByte (BitVec.ofNat 64 (base + i)) = value.extractLsb' (8 * i) 8) :
    hashInput s = ⟨8 * n, value⟩ := by
  dsimp only [hashInput]
  rw [bits]
  apply congrArg (fun v : BitVec (8 * n) => (⟨8 * n, v⟩ : Query))
  have same : (List.range (8 * n)).foldl (fun acc i => acc + if (s.getByte (s.getReg .x10 + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) then 2 ^ i else 0) 0 =
      (List.range (8 * n)).foldl (fun acc i => acc + (value.toNat / 2 ^ (1 * i) % 2 ^ 1) * 2 ^ (1 * i)) 0 := by
    apply Memory.foldl_eq_on
    intro i hi acc
    have index : i < 8 * n := by simpa using hi
    rw [source, ← BitVec.ofNat_add, h (i / 8) (by omega), BitVec.getLsbD_extractLsb']
    simp only [show i % 8 < 8 by omega, decide_true, Bool.true_and,
      show 8 * (i / 8) + i % 8 = i by omega, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, Nat.one_mul, Nat.pow_one]
    have small : value.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
    split <;> simp_all
  rw [same, Memory.digit_fold]
  simp

theorem fold_scale {α : Type} (xs : List α) (f : α → Nat) (scale initial : Nat) :
    xs.foldl (fun acc x => acc + scale * f x) initial = initial + scale * xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing scale initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have add := ih (scale := 1) (initial := f x)
    simp only [Nat.one_mul] at add
    rw [Nat.zero_add, add]
    ring

private theorem byte_bits (value : Byte) :
    (List.range 8).foldl (fun acc i => acc + if value.getLsbD i then 2 ^ i else 0) 0 = value.toNat := by
  have same : (List.range 8).foldl (fun acc i => acc + if value.getLsbD i then 2 ^ i else 0) 0 =
      (List.range 8).foldl (fun acc i => acc + (value.toNat / 2 ^ (1 * i) % 2 ^ 1) * 2 ^ (1 * i)) 0 := by
    apply Memory.foldl_eq_on
    intro i hi acc
    simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, Nat.one_mul, Nat.pow_one]
    have small : value.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
    split <;> simp_all
  rw [same, Memory.digit_fold]
  exact Nat.zero_add _ |>.trans (Nat.mod_eq_of_lt value.isLt)

private theorem shifted_byte_bits (value : Byte) (offset initial : Nat) :
    (List.range 8).foldl (fun acc i => acc + if value.getLsbD i then 2 ^ (offset + i) else 0) initial =
      initial + 2 ^ offset * value.toNat := by
  have same : (List.range 8).foldl (fun acc i => acc + if value.getLsbD i then 2 ^ (offset + i) else 0) initial =
      (List.range 8).foldl (fun acc i => acc + 2 ^ offset * (if value.getLsbD i then 2 ^ i else 0)) initial := by
    apply Memory.foldl_eq_on
    intro i hi acc
    split <;> simp_all [Nat.pow_add]
  rw [same, fold_scale, byte_bits]

/-- Grouping the VM's bit encoding into bytes preserves its exact numeric value. -/
theorem bit_byte_fold (data : Nat → Byte) (n : Nat) :
    (List.range (8 * n)).foldl (fun acc i => acc + if (data (i / 8)).getLsbD (i % 8) then 2 ^ i else 0) 0 =
      (List.range n).foldl (fun acc i => acc + (data i).toNat * 2 ^ (8 * i)) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, List.range_add, List.foldl_append, List.foldl_map, ih]
    rw [List.range_succ (n := n), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have same : ∀ initial,
        (List.range 8).foldl (fun acc i => acc + if (data ((8 * n + i) / 8)).getLsbD ((8 * n + i) % 8) then 2 ^ (8 * n + i) else 0) initial =
        (List.range 8).foldl (fun acc i => acc + if (data n).getLsbD i then 2 ^ (8 * n + i) else 0) initial := by
      intro initial
      apply Memory.foldl_eq_on
      intro i hi acc
      have index : i < 8 := by simpa using hi
      rw [show (8 * n + i) / 8 = n by omega, show (8 * n + i) % 8 = i by omega]
    rw [same, shifted_byte_bits, Nat.mul_comm (2 ^ (8 * n))]

theorem zipIdx_eq_range (data : List Byte) :
    data.zipIdx = (List.range data.length).map (fun i => (getByteAt data i, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range]
    have index : i < data.length := by simpa using hi
    simp [getByteAt, index]

/-- A buffer with these bytes produces precisely the reference scheme's oracle query. -/
theorem hashInput_of_list (s : MachineState) (base : Nat) (data : List Byte)
    (source : s.getReg .x10 = BitVec.ofNat 64 base)
    (bits : (s.getReg .x11).toNat = 8 * data.length)
    (h : ∀ i, (hi : i < data.length) → s.getByte (BitVec.ofNat 64 (base + i)) = data[i]'hi) :
    hashInput s = Hypertree.Reference.packed data := by
  dsimp only [hashInput, Hypertree.Reference.packed]
  rw [bits]
  apply congrArg (fun v : BitVec (8 * data.length) => (⟨8 * data.length, v⟩ : Query))
  apply congrArg (BitVec.ofNat (8 * data.length))
  have same : (List.range (8 * data.length)).foldl (fun acc i => acc + if (s.getByte (s.getReg .x10 + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) then 2 ^ i else 0) 0 =
      (List.range (8 * data.length)).foldl (fun acc i => acc + if (getByteAt data (i / 8)).getLsbD (i % 8) then 2 ^ i else 0) 0 := by
    apply Memory.foldl_eq_on
    intro i hi acc
    have index : i / 8 < data.length := by
      have : i < 8 * data.length := by simpa using hi
      omega
    rw [source, ← BitVec.ofNat_add, h (i / 8) index]
    simp only [getByteAt, dif_pos index]
  rw [same, bit_byte_fold, zipIdx_eq_range, List.foldl_map]

/-- A query is determined by its retained bit length and numeric contents. -/
theorem query_eq (first second : Query) (length : first.1 = second.1)
    (value : first.2.toNat = second.2.toNat) : first = second := by
  rcases first with ⟨n, first⟩
  rcases second with ⟨m, second⟩
  dsimp only at length value
  subst m
  exact congrArg (fun v : BitVec n => (⟨n, v⟩ : Query)) (BitVec.eq_of_toNat_eq value)

/-- Packing the organizer's byte encoding recovers the original value and width. -/
theorem packed_bytes (n : Nat) (value : Bytes n) :
    Hypertree.Reference.packed (bytes value) = ⟨8 * n, value⟩ := by
  dsimp only [Hypertree.Reference.packed]
  rw [Memory.bytes_length]
  apply congrArg (fun v : BitVec (8 * n) => (⟨8 * n, v⟩ : Query))
  rw [zipIdx_eq_range, List.foldl_map, Memory.bytes_length]
  have same : (List.range n).foldl (fun acc i => acc + (getByteAt (bytes value) i).toNat * 2 ^ (8 * i)) 0 =
      (List.range n).foldl (fun acc i => acc + (value.toNat / 2 ^ (8 * i) % 2 ^ 8) * 2 ^ (8 * i)) 0 := by
    apply Memory.foldl_eq_on
    intro i hi acc
    have index : i < n := by simpa using hi
    simp [getByteAt, bytes, index, Nat.shiftRight_eq_div_pow]
  rw [same, Memory.digit_fold]
  simp

/-- info: 'SigGolfCandidate.Serialization.hashInput_of_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hashInput_of_list

end SigGolfCandidate.Serialization
