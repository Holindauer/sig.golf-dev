import SigGolfCandidate.Hypertree.SecurityNonceMonitor

namespace SigGolfCandidate.Hypertree.SecurityNonceMonitor
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem expected_eq {α : Type} (first second : ProbComp α) (same : 𝒮[first] = 𝒮[second])
    (value : α → ENNReal) : expectedValue first value = expectedValue second value := by
  apply expectedValue_congr _ value
  intro output
  exact probOutput_congr rfl same

/-- The recursive deferred-sampling cost is exactly the expected number of
prereveal guesses recorded by the joint experiment. -/
theorem expected_guesses (strategy : Strategy) (cache : NonceCache) :
    expectedValue (experiment strategy cache) (fun result => (result.2 : ENNReal)) = cost cache strategy := by
  induction strategy generalizing cache with
  | done => simp [experiment, play, cost, expectedValue_const NeverFail.probFailure_eq_zero]
  | coin n next ih =>
    rw [expected_eq _ _ (coin_law cache n next), expectedValue_bind]
    simp only [ih, cost]
  | bits next ih =>
    rw [expected_eq _ _ (bits_law cache next), expectedValue_bind]
    simp only [ih, cost]
  | reveal message next ih =>
    cases present : cache message with
    | some nonce => rw [reveal_known cache message next nonce present, ih]; simp only [cost, present]
    | none =>
      rw [expected_eq _ _ (reveal_fresh cache message next present), expectedValue_bind]
      simp only [ih, cost, present]
  | guess message nonce next ih =>
    have exactCost : expectedValue (experiment (.guess message nonce next) cache)
        (fun result => (result.2 : ENNReal)) =
        (if cache message = none then 1 else 0) +
          expectedValue (experiment next cache) (fun result => (result.2 : ENNReal)) := by
      simp only [experiment, play, expectedValue_bind, expectedValue_pure, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, expectedValue_add,
        expectedValue_const NeverFail.probFailure_eq_zero]
    rw [exactCost, ih]
    rfl

noncomputable def risk (strategy : Strategy) (cache : NonceCache) : ENNReal :=
  Pr[fun result => result.1 = true | experiment strategy cache]

private theorem risk_guess_le (cache : NonceCache) (message : Message) (nonce : BitVec 256) (next : Strategy) :
    risk (.guess message nonce next) cache ≤
      (if cache message = none then 1 else 0) / (2 : ENNReal)^256 + risk next cache := by
  have bound := SecurityGraphPassive.passive_or_le ($ᵗ NonceTable)
    (fun table => decide (cache message = none ∧ complete cache table message = nonce))
    (fun table => Prod.fst <$> play (complete cache table) cache next)
  have same : Pr[fun hit => hit = true | (do
      let table ← $ᵗ NonceTable
      let later ← Prod.fst <$> play (complete cache table) cache next
      pure (decide (cache message = none ∧ complete cache table message = nonce) || later))] =
      risk (.guess message nonce next) cache := by
    simp only [risk, experiment, play, probEvent_bind_eq_expectedValue,
      probEvent_pure, map_eq_pure_bind, bind_assoc, pure_bind]
  rw [same] at bound
  simp only [decide_eq_true_eq, guess_density, risk, experiment,
    probEvent_bind_eq_expectedValue, probEvent_map, Function.comp_def] at bound
  simpa only [risk, experiment, probEvent_bind_eq_expectedValue] using bound

/-- Probability of any successful prereveal nonce guess, charged only to the
expected number of such guesses. Earlier misses never condition this bound. -/
theorem risk_le_cost (strategy : Strategy) (cache : NonceCache) :
    risk strategy cache ≤ cost cache strategy / (2 : ENNReal)^256 := by
  induction strategy generalizing cache with
  | done =>
    simp only [risk, experiment, play, cost, probEvent_bind_eq_expectedValue,
      probEvent_pure, Bool.false_eq_true, ite_false]
    rw [expectedValue_const NeverFail.probFailure_eq_zero, ENNReal.zero_div]
  | coin n next ih =>
    rw [risk, probEvent_def, coin_law, ← probEvent_def, probEvent_bind_eq_expectedValue]
    change expectedValue ($ᵗ Fin (n + 1)) (fun answer => risk (next answer) cache) ≤ _
    calc
      _ ≤ expectedValue ($ᵗ Fin (n + 1)) (fun answer => cost cache (next answer) / (2 : ENNReal)^256) :=
        expectedValue_mono _ (fun answer => ih answer cache)
      _ = _ := by simp only [cost, div_eq_mul_inv, expectedValue_mul_const]
  | bits next ih =>
    rw [risk, probEvent_def, bits_law, ← probEvent_def, probEvent_bind_eq_expectedValue]
    change expectedValue ($ᵗ BitVec 256) (fun answer => risk (next answer) cache) ≤ _
    calc
      _ ≤ expectedValue ($ᵗ BitVec 256) (fun answer => cost cache (next answer) / (2 : ENNReal)^256) :=
        expectedValue_mono _ (fun answer => ih answer cache)
      _ = _ := by simp only [cost, div_eq_mul_inv, expectedValue_mul_const]
  | reveal message next ih =>
    cases present : cache message with
    | some nonce =>
      simpa only [risk, reveal_known cache message next nonce present, cost, present] using ih nonce cache
    | none =>
      rw [risk, probEvent_def, reveal_fresh cache message next present, ← probEvent_def,
        probEvent_bind_eq_expectedValue]
      change expectedValue ($ᵗ BitVec 256) (fun nonce => risk (next nonce) (cache.cacheQuery message nonce)) ≤ _
      calc
        _ ≤ expectedValue ($ᵗ BitVec 256)
            (fun nonce => cost (cache.cacheQuery message nonce) (next nonce) / (2 : ENNReal)^256) :=
          expectedValue_mono _ (fun nonce => ih nonce (cache.cacheQuery message nonce))
        _ = _ := by simp only [cost, present, div_eq_mul_inv, expectedValue_mul_const]
  | guess message nonce next ih =>
    calc
      _ ≤ (if cache message = none then 1 else 0) / (2 : ENNReal)^256 + risk next cache :=
        risk_guess_le cache message nonce next
      _ ≤ (if cache message = none then 1 else 0) / (2 : ENNReal)^256 + cost cache next / (2 : ENNReal)^256 :=
        add_le_add le_rfl (ih cache)
      _ = _ := by rw [cost, ENNReal.add_div]

/-- The operational expected-cost form used when combining disjoint query classes. -/
theorem risk_le_expected (strategy : Strategy) (cache : NonceCache) :
    Pr[fun result => result.1 = true | experiment strategy cache] ≤
      expectedValue (experiment strategy cache) (fun result => (result.2 : ENNReal)) / (2 : ENNReal)^256 := by
  rw [expected_guesses]
  exact risk_le_cost strategy cache

/-- Random external views, independent private randomness, and varying disclosed
caches may be averaged without replacing the nonce work by a global budget. -/
theorem weighted_risk_le {α : Type} (draw : ProbComp α) (strategy : α → Strategy)
    (cache : α → NonceCache) :
    expectedValue draw (fun view => risk (strategy view) (cache view)) ≤
      expectedValue draw (fun view => cost (cache view) (strategy view)) / (2 : ENNReal)^256 := by
  calc
    _ ≤ expectedValue draw (fun view => cost (cache view) (strategy view) / (2 : ENNReal)^256) :=
      expectedValue_mono _ (fun view => risk_le_cost (strategy view) (cache view))
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

/-- Operational form for a randomized initial view; the exact work is still
read from the second component of the same joint monitor execution. -/
theorem mixed_risk_le_expected {α : Type} (draw : ProbComp α) (strategy : α → Strategy)
    (cache : α → NonceCache) :
    Pr[fun result => result.1 = true | (do let view ← draw; experiment (strategy view) (cache view))] ≤
      expectedValue (do let view ← draw; experiment (strategy view) (cache view))
        (fun result => (result.2 : ENNReal)) / (2 : ENNReal)^256 := by
  rw [probEvent_bind_eq_expectedValue, expectedValue_bind]
  simp only [expected_guesses]
  exact weighted_risk_le draw strategy cache

/-- A disjoint nonce-query allowance can be substituted after proving its
expected-work bound; no other query class is charged here. -/
theorem risk_le_allowance (strategy : Strategy) (cache : NonceCache) (allowance : ENNReal)
    (work : expectedValue (experiment strategy cache) (fun result => (result.2 : ENNReal)) ≤ allowance) :
    risk strategy cache ≤ allowance / (2 : ENNReal)^256 :=
  (risk_le_expected strategy cache).trans (ENNReal.div_le_div work le_rfl)

end SigGolfCandidate.Hypertree.SecurityNonceMonitor
