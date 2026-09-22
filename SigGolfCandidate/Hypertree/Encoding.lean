import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Hypertree.Reference

/-- Comparing every base-8 digit compares the represented natural numbers. -/
private theorem base8_le (count m n : Nat) (hm : m < 8 ^ count) (hn : n < 8 ^ count)
    (digits : ∀ i, i < count → m / 8 ^ i % 8 ≤ n / 8 ^ i % 8) : m ≤ n := by
  induction count generalizing m n with
  | zero => simp only [pow_zero] at hm hn; omega
  | succ count ih =>
    have hm' : m / 8 < 8 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hm
    have hn' : n / 8 < 8 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hn
    have tails : m / 8 ≤ n / 8 := ih _ _ hm' hn' (by
      intro i hi
      have h := digits (i + 1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h)
    have heads := digits 0 (by omega)
    simp only [pow_zero, Nat.div_one] at heads
    omega

private theorem digit_sum_bound (message : Digest) :
    (∑ i : Fin 43, messageDigit message i) ≤ 301 := by
  calc
    _ ≤ ∑ _i : Fin 43, (7 : Nat) := Finset.sum_le_sum (fun i _ => by
      unfold messageDigit
      have bound := Nat.mod_lt (message.toNat / 8 ^ i.val) (by decide : 0 < 8)
      omega)
    _ = 301 := by simp

/-- A signature cannot be retargeted to a different digest merely by walking every chain forward. This is an encoding property, not the full random-oracle security theorem. -/
theorem digits_antichain (x y : Digest)
    (ordered : ∀ i : Chain, (digit x i).val ≤ (digit y i).val) : x = y := by
  have messages : ∀ i : Fin 43, messageDigit x i ≤ messageDigit y i := by
    intro i
    have h := ordered ⟨i.val, by omega⟩
    simpa only [digit, i.isLt, ↓reduceIte, messageDigit] using h
  have sum_le : (∑ i : Fin 43, messageDigit x i) ≤ ∑ i : Fin 43, messageDigit y i :=
    Finset.sum_le_sum (fun i _ => messages i)
  have checksum_le : checksum x ≤ checksum y := by
    apply base8_le 3
    · unfold checksum
      omega
    · unfold checksum
      omega
    · intro i hi
      have h := ordered ⟨43 + i, by omega⟩
      simpa [digit, show ¬ 43 + i < 43 by omega] using h
  have hx := digit_sum_bound x
  have hy := digit_sum_bound y
  have same_sum : (∑ i : Fin 43, messageDigit x i) = ∑ i : Fin 43, messageDigit y i := by
    unfold checksum at checksum_le
    omega
  have same_digits := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 43))) => messages i)).mp same_sum
  have xbound : x.toNat < 8 ^ 43 := lt_of_lt_of_le x.isLt (by decide)
  have ybound : y.toNat < 8 ^ 43 := lt_of_lt_of_le y.isLt (by decide)
  apply BitVec.eq_of_toNat_eq
  apply Nat.le_antisymm
  · apply base8_le 43 _ _ xbound ybound
    intro i hi
    exact (same_digits ⟨i, hi⟩ (by simp)).le
  · apply base8_le 43 _ _ ybound xbound
    intro i hi
    exact (same_digits ⟨i, hi⟩ (by simp)).ge

/-- Changing the digest requires an earlier position in at least one revealed chain. -/
theorem distinct_digest_has_earlier_digit (x y : Digest) (different : x ≠ y) :
    ∃ i : Chain, (digit y i).val < (digit x i).val := by
  by_contra h
  push Not at h
  exact different (digits_antichain x y h)

/-- info: 'SigGolfCandidate.Hypertree.Reference.digits_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digits_antichain

end SigGolfCandidate.Hypertree.Reference
