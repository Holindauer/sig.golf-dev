import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Hypertree.ChainCost
open Reference

/-- Hash calls spent recovering the first `count` WOTS chains. -/
def chainPrefix (message : Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (7 - (digit message ⟨i % 46, Nat.mod_lt _ (by decide)⟩).val)

@[simp] theorem chainPrefix_zero (message : Digest) : chainPrefix message 0 = 0 := by
  simp [chainPrefix]

theorem chainPrefix_succ (message : Digest) (n : Nat) (bound : n < 46) :
    chainPrefix message (n+1) = chainPrefix message n + (7 - (digit message ⟨n,bound⟩).val) := by
  simp [chainPrefix, Finset.sum_range_succ, Nat.mod_eq_of_lt bound]

/-- The checksum prevents all 46 chains from simultaneously requiring seven hashes. -/
theorem digit_sum_lower (message : Digest) :
    14 ≤ ∑ i : Chain, (digit message i).val := by
  let total := ∑ i : Fin 43, messageDigit message i
  have total_le : total ≤ 301 := by
    calc
      total ≤ ∑ _i : Fin 43, (7 : Nat) := Finset.sum_le_sum (fun i _ => by
        unfold messageDigit
        have := Nat.mod_lt (message.toNat / 8 ^ i.val) (by decide : 0 < 8)
        omega)
      _ = 301 := by simp
  have split_sum : (∑ i : Chain, (digit message i).val) =
      total + (301-total)%8 + ((301-total)/8)%8 + ((301-total)/64)%8 := by
    rw [Fin.sum_univ_add (a := 43) (b := 3)]
    have first : (∑ i : Fin 43, (digit message (Fin.castAdd 3 i)).val) = total := by
      apply Finset.sum_congr rfl
      intro i _
      simp [digit, messageDigit]
    rw [first]
    simp [Fin.sum_univ_succ, digit, checksum, total, Nat.add_assoc]
  rw [split_sum]
  by_cases large : 14 ≤ total
  · omega
  · have small : total < 14 := by omega
    interval_cases total <;> norm_num

/-- At most 308 chain HASH calls per upper leaf, uniformly over all digests. -/
theorem chainPrefix_full_le (message : Digest) : chainPrefix message 46 ≤ 308 := by
  have full : chainPrefix message 46 = ∑ i : Chain, (7 - (digit message i).val) := by
    unfold chainPrefix
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.mod_eq_of_lt i.isLt]
  have total : (∑ i : Chain, (7 - (digit message i).val)) +
      (∑ i : Chain, (digit message i).val) = 322 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Chain, (7 : Nat) := by
        apply Finset.sum_congr rfl
        intro i _
        have := (digit message i).isLt
        omega
      _ = 322 := by simp
  have lower := digit_sum_lower message
  omega

/-- info: 'SigGolfCandidate.Hypertree.ChainCost.chainPrefix_full_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainPrefix_full_le

end SigGolfCandidate.Hypertree.ChainCost
