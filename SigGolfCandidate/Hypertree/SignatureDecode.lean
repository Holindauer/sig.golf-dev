import SigGolfCandidate.Hypertree.Signature

namespace SigGolfCandidate.Hypertree.SignatureEncoding
open SigGolf Reference

def slice {n : Nat} (value : Bytes n) (start size : Nat) : Bytes size :=
  value.extractLsb' (8 * start) (8 * size)

/-- Byte-aligned bit extraction is exactly list slicing of the organizer's encoding. -/
theorem bytes_slice {n : Nat} (value : Bytes n) (start size : Nat) (bound : start + size ≤ n) :
    bytes (slice value start size) = ((bytes value).drop start).take size := by
  apply List.ext_getElem
  · simp only [Memory.bytes_length, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    have index : i < size := by simpa only [Memory.bytes_length] using hi
    simp only [bytes, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [slice, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      show 8 * i + j < 8 * size by omega, decide_true, Bool.true_and]
    congr 1
    omega

theorem ofFn_nat {α : Type} (n : Nat) (f : Nat → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem chunks_reassemble {α : Type} (data : List α) (start width count : Nat) :
    (List.range count).flatMap (fun i => (data.drop (start + width * i)).take width) =
      (data.drop start).take (width * count) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
    rw [Nat.mul_succ, List.take_add, List.drop_drop]

theorem flatMap_eq_on {α β : Type} (data : List α) (f g : α → List β)
    (h : ∀ x, x ∈ data → f x = g x) : data.flatMap f = data.flatMap g := by
  induction data with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

def decodeLayer (value : Bytes signatureBytes) (index : Nat) : LayerSignature where
  values := fun chain => slice value (64 + 752 * index + 16 * chain.val) 16
  sibling := slice value (64 + 752 * index + 736) 16

def decode (value : Bytes signatureBytes) : Compact where
  randomizer := slice value 0 32
  bottom := slice value 32 16
  sibling := slice value 48 16
  upper := (List.range 159).map (decodeLayer value)

theorem decode_valid (value : Bytes signatureBytes) : (decode value).Valid := by
  simp [decode, Compact.Valid]

theorem decodeLayer_bytes (value : Bytes signatureBytes) (index : Nat) (hi : index < 159) :
    layerBytes (decodeLayer value index) = ((bytes value).drop (64 + 752 * index)).take 752 := by
  dsimp only [layerBytes, decodeLayer]
  rw [ofFn_nat 46 (fun i => slice value (64 + 752 * index + 16 * i) 16), List.flatMap_map]
  have first : (List.range 46).flatMap (fun i => bytes (slice value (64 + 752 * index + 16 * i) 16)) =
      (List.range 46).flatMap (fun i => ((bytes value).drop (64 + 752 * index + 16 * i)).take 16) := by
    apply flatMap_eq_on
    intro i hi'
    have bound : i < 46 := by simpa using hi'
    apply bytes_slice
    change 64 + 752 * index + 16 * i + 16 ≤ 119632
    omega
  rw [first, chunks_reassemble, bytes_slice value (64 + 752 * index + 736) 16 (by change 64 + 752 * index + 736 + 16 ≤ 119632; omega)]
  simpa only [List.drop_drop] using (List.take_add (l := (bytes value).drop (64 + 752 * index)) (i := 736) (j := 16)).symm

theorem decode_encode (value : Bytes signatureBytes) : (decode value).encode = bytes value := by
  dsimp only [Compact.encode, decode]
  rw [List.flatMap_map]
  have upper : (List.range 159).flatMap (fun i => layerBytes (decodeLayer value i)) =
      ((bytes value).drop 64).take (752 * 159) := by
    rw [← chunks_reassemble]
    apply flatMap_eq_on
    intro i hi
    exact decodeLayer_bytes value i (by simpa using hi)
  rw [upper, bytes_slice value 0 32 (by decide), bytes_slice value 32 16 (by decide),
    bytes_slice value 48 16 (by decide), List.drop_zero]
  rw [← List.take_add (i := 32) (j := 16), ← List.take_add (i := 48) (j := 16),
    ← List.take_add (i := 64) (j := 752 * 159)]
  apply List.take_of_length_le
  rw [Memory.bytes_length (n := signatureBytes)]
  decide

/-- Every fixed-size input has exactly one canonical interpretation; no signature bits are ignored. -/
theorem decode_wire (value : Bytes signatureBytes) : (decode value).wire (decode_valid value) = value := by
  apply SecurityPacking.bytes_injective signatureBytes
  rw [Compact.wire_bytes, decode_encode]

/-- Canonical encoding and decoding are mutual inverses. -/
theorem wire_decode (signature : Compact) (valid : signature.Valid) : decode (signature.wire valid) = signature := by
  apply Compact.encode_injective
  rw [decode_encode, Compact.wire_bytes]

/-- info: 'SigGolfCandidate.Hypertree.SignatureEncoding.decode_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decode_wire

end SigGolfCandidate.Hypertree.SignatureEncoding
