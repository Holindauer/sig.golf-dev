import SigGolfCandidate.Hypertree.SecurityBudget
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.Hypertree.SecurityQueryCosts
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityGameHop SecuritySeparation SecurityBudget
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- The two main query classes are disjoint by construction. -/
noncomputable def secretKeyCost (query : GameWorld.Domain) : Nat := (prependPublic query []).length
noncomputable def otherCost (query : GameWorld.Domain) : Nat := charge query - secretKeyCost query

theorem secretKeyCost_le (query : GameWorld.Domain) : secretKeyCost query ≤ charge query := by
  simpa [secretKeyCost] using prependPublic_length_le query []

theorem secretKeyCost_add_otherCost (query : GameWorld.Domain) :
    secretKeyCost query + otherCost query = charge query := by
  unfold otherCost
  exact Nat.add_sub_of_le (secretKeyCost_le query)

theorem prependPublic_length (query : GameWorld.Domain) (inputs : List Query) :
    (prependPublic query inputs).length = inputs.length + secretKeyCost query := by
  cases query with
  | inl n => simp [prependPublic, secretKeyCost]
  | inr query =>
    cases query with
    | inl slot => simp [prependPublic, secretKeyCost]
    | inr input => simp only [prependPublic, secretKeyCost]; split <;> simp_all

def costed {α : Type} (cost : GameWorld.Domain → Nat) (program : OracleComp GameWorld α) :
    OracleComp GameWorld (α × Nat) :=
  OracleComp.construct (fun value => pure (value, 0))
    (fun query _ next => do
      let answer ← liftM (GameWorld.query query)
      let result ← next answer
      return (result.1, result.2 + cost query)) program

@[simp] theorem costed_pure {α : Type} (cost : GameWorld.Domain → Nat) (value : α) :
    costed cost (pure value) = pure (value, 0) := rfl

theorem costed_query_bind {α : Type} (cost : GameWorld.Domain → Nat) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    costed cost (liftM (GameWorld.query query) >>= next) = (do
      let answer ← liftM (GameWorld.query query)
      let result ← costed cost (next answer)
      return (result.1, result.2 + cost query)) := rfl

@[simp] theorem costed_charge {α : Type} (program : OracleComp GameWorld α) :
    costed charge program = counted program := rfl

theorem costed_secretKey {α : Type} (program : OracleComp GameWorld α) :
    costed secretKeyCost program = (fun result => (result.1, result.2.length)) <$> tracePublic program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [costed_query_bind, tracePublic_query_bind, map_bind, ih,
      bind_pure_comp, Functor.map_map, prependPublic_length]

noncomputable def expectedCost {α : Type} (cost : GameWorld.Domain → Nat)
    (program : OracleComp GameWorld α) (cache : SplitCache) : ENNReal :=
  expectedValue ((simulateQ idealGameOracle (costed cost program)).run' cache)
    (fun result => (result.2 : ENNReal))

@[simp] theorem expectedCost_pure {α : Type} (cost : GameWorld.Domain → Nat) (value : α)
    (cache : SplitCache) : expectedCost cost (pure value) cache = 0 := by simp [expectedCost]

private theorem run'_query_bind {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) (cache : SplitCache) :
    (simulateQ idealGameOracle (liftM (GameWorld.query query) >>= next)).run' cache =
      ((idealGameOracle query).run cache >>= fun result =>
        (simulateQ idealGameOracle (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

theorem expectedCost_query_bind {α : Type} (cost : GameWorld.Domain → Nat)
    (query : GameWorld.Domain) (next : GameWorld.Range query → OracleComp GameWorld α)
    (cache : SplitCache) :
    expectedCost cost (liftM (GameWorld.query query) >>= next) cache =
      expectedValue ((idealGameOracle query).run cache)
        (fun result => expectedCost cost (next result.1) result.2 + cost query) := by
  simp only [expectedCost, costed_query_bind, run'_query_bind, expectedValue_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    expectedValue_map, Nat.cast_add, expectedValue_add]
  simp only [expectedValue_const NeverFail.probFailure_eq_zero]

/-- Expected costs add even when the strategy decides later query classes adaptively. -/
theorem expectedCost_add {α : Type} (first second : GameWorld.Domain → Nat)
    (program : OracleComp GameWorld α) (cache : SplitCache) :
    expectedCost (fun query => first query + second query) program cache =
      expectedCost first program cache + expectedCost second program cache := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
    simp only [expectedCost_query_bind, ih, Nat.cast_add, ← expectedValue_add]
    congr 1
    funext result
    ac_rfl

/-- The secret key-erasure penalty's expectation is exactly the cost of the secret key query class. -/
theorem expectedCost_secretKey {α : Type} (program : OracleComp GameWorld α) (cache : SplitCache) :
    expectedCost secretKeyCost program cache = expectedSecretKeyQueries program cache := by
  simp only [expectedCost, costed_secretKey, simulateQ_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map, expectedValue_map]
  change _ = expectedValue ((simulateQ idealGameOracle (tracePublic program)).run' cache)
    (fun result => (result.2.length : ENNReal))
  simp only [StateT.run'_eq, expectedValue_map]

/-- The two expectations spend one total H-call budget, with no extra factor two. -/
theorem expected_main_costs {α : Type} (program : OracleComp GameWorld α) (cache : SplitCache) :
    expectedSecretKeyQueries program cache + expectedCost otherCost program cache =
      expectedCost charge program cache := by
  rw [← expectedCost_secretKey, ← expectedCost_add]
  congr 1
  funext query
  exact secretKeyCost_add_otherCost query

theorem cutoff_counted_bound {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) (budget : Nat) :
    ∀ result ∈ support ((simulateQ idealGameOracle (counted (cutoff program budget))).run' cache),
      result.2 ≤ budget := by
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value => simp
  | query_bind query next ih =>
    rw [cutoff_query_bind]
    split
    next allowed =>
      intro result hr
      rw [counted_query_bind, run'_query_bind, mem_support_bind_iff] at hr
      obtain ⟨step, _, hr⟩ := hr
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨tail, ht, rfl⟩ := hr
      have bound := ih step.1 step.2 (budget - charge query)
      have htail : tail.1.2 ≤ budget - charge query := by
        apply bound
        rw [StateT.run'_eq, support_map, Set.mem_image]
        exact ⟨tail, ht, rfl⟩
      dsimp
      omega
    next exhausted => simp

/-- Every adversary, after the organizer-style total-call cutoff, has one shared
expected budget for the secret key and complementary query classes. -/
theorem expected_main_costs_cutoff_le {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) (budget : Nat) :
    expectedSecretKeyQueries (cutoff program budget) cache +
      expectedCost otherCost (cutoff program budget) cache ≤ budget := by
  rw [expected_main_costs]
  unfold expectedCost
  rw [costed_charge]
  apply expectedValue_le_of_support
  intro result hr
  exact_mod_cast cutoff_counted_bound program cache budget result hr

/-- Explicit remaining reduction obligation: once the ideal forgery event is
bounded by the complementary-query expectation plus its index/nonce remainder,
the actual secretKeyed game spends Q/2^128 on both main classes together. This theorem
does not assert that the ideal forgery bound has been established. -/
theorem compose_secretKey_and_other {α : Type} (program : OracleComp GameWorld α)
    (budget : Nat) (event : α → Prop) (remainder : ENNReal)
    (idealBound :
      Pr[fun value => ∃ x, value = some x ∧ event x |
        (simulateQ idealGameOracle (cutoff program budget)).run' (∅, ∅)] ≤
      expectedCost otherCost (cutoff program budget) (∅, ∅) / (2 : ENNReal) ^ 128 + remainder) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) (counted program)).run' ∅] ≤
        (budget : ENNReal) / 2 ^ 128 + remainder := by
  have hop := prob_real_le_ideal_add_expected_secretKey (cutoff program budget)
    (fun value => ∃ x, value = some x ∧ event x)
  simp only [probEvent_bind_eq_tsum, prob_cutoff_eq_counted] at hop
  have ideal := idealBound
  rw [prob_cutoff_eq_counted] at ideal
  have costs := expected_main_costs_cutoff_le program (∅, ∅) budget
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ (expectedCost otherCost (cutoff program budget) (∅, ∅) / (2 : ENNReal) ^ 128 + remainder) +
        expectedSecretKeyQueries (cutoff program budget) (∅, ∅) / (2 : ENNReal) ^ 128 :=
      hop.trans (add_le_add ideal le_rfl)
    _ = (expectedSecretKeyQueries (cutoff program budget) (∅, ∅) +
        expectedCost otherCost (cutoff program budget) (∅, ∅)) / (2 : ENNReal) ^ 128 + remainder := by
      rw [ENNReal.add_div]
      ac_rfl
    _ ≤ _ := add_le_add (ENNReal.div_le_div costs le_rfl) le_rfl

end SigGolfCandidate.Hypertree.SecurityQueryCosts
