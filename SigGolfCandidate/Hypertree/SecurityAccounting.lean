import SigGolf.Security

namespace SigGolfCandidate.Hypertree.SecurityAccounting

/-- Removing one failed guess from a uniform secret's remaining support does not
cost a factor two. This is the induction identity for exact guessing bounds. -/
theorem withoutReplacement_step (remaining trials : ℝ)
    (hremaining : 1 < remaining) :
    1 / remaining + (1 - 1 / remaining) * ((trials - 1) / (remaining - 1)) =
      trials / remaining := by
  have h0 : remaining ≠ 0 := by linarith
  have h1 : remaining - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- A trial against an independent hash target can be interleaved with secret key
guesses without charging both classes the entire query budget. -/
theorem independentTarget_step (remaining trials hazard : ℝ)
    (hremaining : 0 < remaining) (htrials : 1 ≤ trials) (hbudget : trials ≤ remaining)
    (hhazard : hazard ≤ 1 / remaining) :
    hazard + (1 - hazard) * ((trials - 1) / remaining) ≤ trials / remaining := by
  have htail : 0 ≤ (trials - 1) / remaining := div_nonneg (by linarith) hremaining.le
  have htail1 : (trials - 1) / remaining ≤ 1 := by
    apply (div_le_one hremaining).2
    linarith
  have h := mul_le_mul_of_nonneg_right hhazard (sub_nonneg.mpr htail1)
  have hid : 1 / remaining + (1 - 1 / remaining) * ((trials - 1) / remaining) ≤
      trials / remaining := by
    have hprod := mul_nonneg (one_div_nonneg.mpr hremaining.le) htail
    have heq : 1 / remaining + (trials - 1) / remaining = trials / remaining := by
      rw [← add_div]
      congr 1
      ring
    nlinarith
  nlinarith

/-- An abstract adaptive search. `secretKey` removes one unsuccessful secret guess;
`target` tests one independent uniform hash value; `mix` permits private branching.
Connecting the real random-oracle experiment to this abstraction is a separate obligation. -/
inductive Search where
  | stop
  | secretKey (next : Search)
  | target (next : Search)
  | mix (probability : ℝ) (left right : Search)

def Search.queries : Search → Nat
  | .stop => 0
  | .secretKey next | .target next => next.queries + 1
  | .mix _ left right => max left.queries right.queries

def Search.Valid : Search → Prop
  | .stop => True
  | .secretKey next | .target next => next.Valid
  | .mix p left right => 0 ≤ p ∧ p ≤ 1 ∧ left.Valid ∧ right.Valid

/-- Risk under fresh uniform targets and a secret key uniform over the remaining
support. Secret key successes and target successes terminate the search immediately. -/
noncomputable def Search.risk (space : Nat) : Nat → Search → ℝ
  | _, .stop => 0
  | remaining, .secretKey next =>
      1 / remaining + (1 - 1 / remaining) * next.risk space (remaining - 1)
  | remaining, .target next =>
      1 / space + (1 - 1 / space) * next.risk space remaining
  | remaining, .mix p left right =>
      p * left.risk space remaining + (1 - p) * right.risk space remaining

/-- Exact combined query budget for the abstract adaptive search. In particular,
starting at `remaining = space` costs `queries / space`, not twice that value. -/
theorem Search.risk_le (search : Search) (space remaining : Nat)
    (valid : search.Valid) (positive : 0 < remaining) (support : remaining ≤ space)
    (budget : search.queries ≤ remaining) :
    search.risk space remaining ≤ search.queries / (remaining : ℝ) := by
  induction search generalizing remaining with
  | stop => simp [Search.risk, Search.queries]
  | secretKey next ih =>
    simp only [Search.queries] at budget ⊢
    simp only [Search.risk]
    by_cases hlast : remaining = 1
    · subst remaining
      simp only [Nat.cast_one, div_one, sub_self, zero_mul, add_zero]
      have : next.queries = 0 := by omega
      simp [this]
    · have hr : 1 < (remaining : ℝ) := by exact_mod_cast (show 1 < remaining by omega)
      have hnext := ih (remaining - 1) valid (by omega) (by omega) (by omega)
      have hcast : ((remaining - 1 : Nat) : ℝ) = (remaining : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast] at hnext
      have hcoef : 0 ≤ 1 - 1 / (remaining : ℝ) := by
        apply sub_nonneg.mpr
        exact (div_le_one (by linarith)).2 (by linarith)
      calc
        _ ≤ 1 / (remaining : ℝ) + (1 - 1 / (remaining : ℝ)) *
            (next.queries / ((remaining : ℝ) - 1)) := by
              have hmul := mul_le_mul_of_nonneg_left hnext hcoef
              linarith
        _ = (next.queries + 1 : ℕ) / (remaining : ℝ) := by
          convert withoutReplacement_step (remaining : ℝ) (next.queries + 1) hr using 1 <;>
            push_cast <;> ring
  | target next ih =>
    simp only [Search.queries] at budget ⊢
    simp only [Search.risk]
    have hnext := ih remaining valid positive support (by omega)
    have hr : 0 < (remaining : ℝ) := by exact_mod_cast positive
    have hs : 0 < (space : ℝ) := lt_of_lt_of_le hr (by exact_mod_cast support)
    have hcoef : 0 ≤ 1 - 1 / (space : ℝ) := by
      apply sub_nonneg.mpr
      apply (div_le_one hs).2
      exact_mod_cast (show 1 ≤ space by omega)
    calc
      _ ≤ 1 / (space : ℝ) + (1 - 1 / (space : ℝ)) *
          (next.queries / (remaining : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hnext hcoef
            linarith
      _ ≤ (next.queries + 1 : ℕ) / (remaining : ℝ) := by
        have h := independentTarget_step (remaining : ℝ) (next.queries + 1)
          (1 / (space : ℝ)) hr (by have := Nat.cast_nonneg (α := ℝ) next.queries; linarith) (by exact_mod_cast budget)
          (one_div_le_one_div_of_le hr (by exact_mod_cast support))
        simpa using h
  | mix p left right ihl ihr =>
    obtain ⟨hp, hp1, hleft, hright⟩ := valid
    have hb : max left.queries right.queries ≤ remaining := budget
    have hl := ihl remaining hleft positive support (le_trans (le_max_left _ _) hb)
    have hr := ihr remaining hright positive support (le_trans (le_max_right _ _) hb)
    have hden : 0 ≤ (remaining : ℝ) := Nat.cast_nonneg _
    have hl' : left.risk space remaining ≤ max left.queries right.queries / (remaining : ℝ) :=
      hl.trans (div_le_div_of_nonneg_right (by exact_mod_cast (le_max_left left.queries right.queries)) hden)
    have hr' : right.risk space remaining ≤ max left.queries right.queries / (remaining : ℝ) :=
      hr.trans (div_le_div_of_nonneg_right (by exact_mod_cast (le_max_right left.queries right.queries)) hden)
    have h1 := mul_le_mul_of_nonneg_left hl' hp
    have h2 := mul_le_mul_of_nonneg_left hr' (sub_nonneg.mpr hp1)
    simp only [Search.risk, Search.queries]
    nlinarith

/-- Initial uniform support gives a single linear bound across both query kinds. -/
theorem Search.initial_risk_le (search : Search) (space budget : Nat)
    (valid : search.Valid) (positive : 0 < space)
    (queries : search.queries ≤ budget) (withinSpace : budget ≤ space) :
    search.risk space space ≤ budget / (space : ℝ) := by
  exact (search.risk_le space space valid positive le_rfl (queries.trans withinSpace)).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast queries) (Nat.cast_nonneg _))

/-- info: 'SigGolfCandidate.Hypertree.SecurityAccounting.Search.initial_risk_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Search.initial_risk_le

end SigGolfCandidate.Hypertree.SecurityAccounting
