import SigGolfCandidate.Hypertree.SecurityIndexProgram
import SigGolfCandidate.Hypertree.SecurityNonceMonitorCost

namespace SigGolfCandidate.Hypertree.SecuritySharedBudget
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

/-- Disjoint public-query classes, counted in one common passive simulation. -/
structure Counts where
  seed : Nat
  graph : Nat
  index : Nat

def Counts.total (counts : Counts) : Nat := counts.seed + counts.graph + counts.index

noncomputable def weight (counts : Counts) : ENNReal :=
  (counts.seed : ENNReal)/2^128 + 2*(counts.graph : ENNReal)/2^128 +
    (counts.index : ENNReal)/2^256 + (counts.index : ENNReal)/2^136

theorem weight_le (counts : Counts) : weight counts ≤ (counts.total : ENNReal)/2^127 := by
  have seed : (counts.seed : ENNReal)/2^128 ≤ 2*(counts.seed : ENNReal)/2^128 := by
    apply ENNReal.div_le_div _ le_rfl
    rw [two_mul]
    exact le_add_right le_rfl
  have nonce : (counts.index : ENNReal)/2^256 ≤ (counts.index : ENNReal)/2^128 :=
    ENNReal.div_le_div le_rfl (by norm_num)
  have index : (counts.index : ENNReal)/2^136 ≤ (counts.index : ENNReal)/2^128 :=
    ENNReal.div_le_div le_rfl (by norm_num)
  calc
    _ ≤ 2*(counts.seed : ENNReal)/2^128 + 2*(counts.graph : ENNReal)/2^128 +
      (counts.index : ENNReal)/2^128 + (counts.index : ENNReal)/2^128 :=
        add_le_add (add_le_add (add_le_add seed le_rfl) nonce) index
    _ = 2*(counts.total : ENNReal)/2^128 := by
      simp only [Counts.total, Nat.cast_add, div_eq_mul_inv]
      ring
    _ = _ := by
      apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
      have powers : (2 : ENNReal)^127 * 2 = 2^128 := by norm_num
      rw [← mul_assoc, powers, mul_comm]

/-- All expectations must be under the same simulation. A pathwise total-call
cutoff then pays for all monitored failure events together. -/
theorem expected_weight_le {α : Type} (simulation : ProbComp α) (counts : α → Counts) (budget : Nat)
    (bounded : ∀ result ∈ support simulation, (counts result).total ≤ budget) :
    expectedValue simulation (fun result => weight (counts result)) ≤ (budget : ENNReal)/2^127 := by
  apply expectedValue_le_of_support
  intro result member
  exact (weight_le (counts result)).trans (ENNReal.div_le_div (by exact_mod_cast bounded result member) le_rfl)

theorem prob_union_le {α : Type} (simulation : ProbComp α) (counts : α → Counts) (budget : Nat)
    (seedBad graphBad nonceBad indexBad : α → Prop)
    (bounded : ∀ result ∈ support simulation, (counts result).total ≤ budget)
    (seedBound : Pr[seedBad | simulation] ≤ expectedValue simulation (fun result => ((counts result).seed : ENNReal)/2^128))
    (graphBound : Pr[graphBad | simulation] ≤ expectedValue simulation (fun result => 2*((counts result).graph : ENNReal)/2^128))
    (nonceBound : Pr[nonceBad | simulation] ≤ expectedValue simulation (fun result => ((counts result).index : ENNReal)/2^256))
    (indexBound : Pr[indexBad | simulation] ≤ expectedValue simulation (fun result => ((counts result).index : ENNReal)/2^136)) :
    Pr[fun result => seedBad result ∨ graphBad result ∨ nonceBad result ∨ indexBad result | simulation] ≤
      (budget : ENNReal)/2^127 := by
  have union : Pr[fun result => seedBad result ∨ graphBad result ∨ nonceBad result ∨ indexBad result | simulation] ≤
      Pr[seedBad | simulation] + Pr[graphBad | simulation] + Pr[nonceBad | simulation] + Pr[indexBad | simulation] := by
    calc
      _ ≤ Pr[seedBad | simulation] + Pr[fun result => graphBad result ∨ nonceBad result ∨ indexBad result | simulation] := (probEvent_or_le simulation _ _)
      _ ≤ Pr[seedBad | simulation] + (Pr[graphBad | simulation] + Pr[fun result => nonceBad result ∨ indexBad result | simulation]) :=
        add_le_add le_rfl (probEvent_or_le simulation _ _)
      _ ≤ Pr[seedBad | simulation] + (Pr[graphBad | simulation] + (Pr[nonceBad | simulation] + Pr[indexBad | simulation])) :=
        add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le simulation _ _))
      _ = _ := by ac_rfl
  calc
    _ ≤ _ := union
    _ ≤ expectedValue simulation (fun result => ((counts result).seed : ENNReal)/2^128) +
      expectedValue simulation (fun result => 2*((counts result).graph : ENNReal)/2^128) +
      expectedValue simulation (fun result => ((counts result).index : ENNReal)/2^256) +
      expectedValue simulation (fun result => ((counts result).index : ENNReal)/2^136) :=
        add_le_add (add_le_add (add_le_add seedBound graphBound) nonceBound) indexBound
    _ = expectedValue simulation (fun result => weight (counts result)) := by
      simp only [weight, expectedValue_add]
    _ ≤ _ := expected_weight_le simulation counts budget bounded

/-- info: 'SigGolfCandidate.Hypertree.SecuritySharedBudget.prob_union_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prob_union_le
end SigGolfCandidate.Hypertree.SecuritySharedBudget
