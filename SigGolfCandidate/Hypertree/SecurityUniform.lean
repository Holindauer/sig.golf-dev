import SigGolf.Security
import ToMathlib.Data.BitVec

namespace SigGolfCandidate.Hypertree.SecurityUniform
open OracleComp OracleSpec

/-- Split a hash answer into low and high bits, without dropping entropy. -/
def splitBits (high low : Nat) : BitVec (high + low) ≃ BitVec low × BitVec high where
  toFun x := (x.extractLsb' 0 low, x.extractLsb' low high)
  invFun x := x.2 ++ x.1
  left_inv x := BitVec.extractLsb'_append_extractLsb'
  right_inv x := by
    simp [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

/-- Truncation of a uniform hash answer is exactly uniform, at arbitrary widths. -/
theorem evalSPMF_extract_uniform (high low : Nat) :
    𝒮[(fun x : BitVec (high + low) => x.extractLsb' 0 low) <$> ($ᵗ BitVec (high + low))] =
      𝒮[$ᵗ BitVec low] := by
  have split := evalSPMF_map_bijective_uniform_cross (BitVec (high + low))
    (splitBits high low) (splitBits high low).bijective
  calc
    _ = 𝒮[Prod.fst <$> ((splitBits high low) <$> ($ᵗ BitVec (high + low)))] := by
      simp [Functor.map_map, splitBits]
    _ = 𝒮[Prod.fst <$> ($ᵗ (BitVec low × BitVec high))] := by
      rw [evalSPMF_map, split, ← evalSPMF_map]
    _ = _ := evalSPMF_map_fst_uniformSample_prod

/-- A fresh truncated hash hits any fixed finite set with its exact target density. -/
theorem prob_extract_mem (high low : Nat) (targets : Finset (BitVec low)) :
    Pr[fun x : BitVec (high + low) => x.extractLsb' 0 low ∈ targets |
      ($ᵗ BitVec (high + low))] = (targets.card : ENNReal) / 2 ^ low := by
  change Pr[(fun x => x ∈ targets) ∘ (fun x : BitVec (high + low) => x.extractLsb' 0 low) |
    ($ᵗ BitVec (high + low))] = _
  rw [← probEvent_map]
  rw [probEvent_def, evalSPMF_extract_uniform, ← probEvent_def]
  rw [probEvent_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  simp

/-- Full-width randomizer guesses have density `card / 2^256`. -/
theorem prob_randomizer_mem (targets : Finset (BitVec 256)) :
    Pr[fun x => x ∈ targets | ($ᵗ BitVec 256)] = (targets.card : ENNReal) / 2 ^ 256 := by
  rw [probEvent_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  simp

end SigGolfCandidate.Hypertree.SecurityUniform
