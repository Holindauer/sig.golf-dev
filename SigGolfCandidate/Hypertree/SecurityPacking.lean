import SigGolfCandidate.Hypertree.Reference
import Mathlib.Data.Nat.Digits.Lemmas

namespace SigGolfCandidate.Hypertree.SecurityPacking
open SigGolf Reference
set_option maxRecDepth 4096

private theorem packed_sum (data : List Byte) :
    data.zipIdx.foldl (fun acc entry => acc + entry.1.toNat * 2 ^ (8 * entry.2)) 0 =
      Nat.ofDigits 256 (data.map BitVec.toNat) := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_zipIdx_map, List.zipIdx_map,
    List.map_map, List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext acc entry
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  rw [pow_mul]
  rfl

private theorem digits_bound (data : List Byte) :
    Nat.ofDigits 256 (data.map BitVec.toNat) < 2 ^ (8 * data.length) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (by decide)
    (l := data.map BitVec.toNat) (by
      intro value hv
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv
      exact byte.isLt)
  simpa [List.length_map, pow_mul] using h

/-- The exact reference packing retains every input byte; its length is part of the query. -/
theorem packed_injective : Function.Injective packed := by
  intro first second heq
  have hlength : first.length = second.length := by
    have h := congrArg Sigma.fst heq
    change 8 * first.length = 8 * second.length at h
    omega
  have hvalue := congrArg (fun q : Query => q.2.toNat) heq
  change (first.zipIdx.foldl _ 0) % 2 ^ (8 * first.length) =
    (second.zipIdx.foldl _ 0) % 2 ^ (8 * second.length) at hvalue
  rw [packed_sum, packed_sum, Nat.mod_eq_of_lt (digits_bound first),
    Nat.mod_eq_of_lt (digits_bound second)] at hvalue
  have hmap := Nat.ofDigits_inj_of_len_eq (by decide : 1 < 256)
    (by simpa using hlength)
    (by intro value hv; obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv; exact byte.isLt)
    (by intro value hv; obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv; exact byte.isLt) hvalue
  exact (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) hmap

/-- The organizer's little-endian byte encoding is injective at every fixed width. -/
theorem bytes_injective (n : Nat) : Function.Injective (bytes (n := n)) := by
  intro first second heq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbyte : i / 8 < n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have hv := congrArg (fun data : List Byte => data[i / 8]?) heq
  simp [bytes, hbyte] at hv
  have hb := congrArg (fun byte : Byte => byte.getLsbD (i % 8)) hv
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and] at hb
  have hidx : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hidx] using hb

end SigGolfCandidate.Hypertree.SecurityPacking
