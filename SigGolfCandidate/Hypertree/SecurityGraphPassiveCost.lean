import SigGolfCandidate.Hypertree.SecurityGraphPassive

namespace SigGolfCandidate.Hypertree.SecurityGraphPassiveCost
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Actual number of tests along the passive strategy's random path. Flags are
not inspected, so the count follows exactly the same adaptive disclosures. -/
noncomputable def tests (table : PointTable) : QueryCache PointSpec → Strategy → ProbComp Nat
  | _, .done => pure 0
  | cache, .reveal point next => tests table (cache.cacheQuery point (table point)) (next (table point))
  | cache, .guess _ _ next => (fun n => n + 1) <$> tests table cache next
  | cache, .collision _ next => do
      let answer ← $ᵗ BitVec 256
      (fun n => n + 1) <$> tests table cache (next answer)
  | cache, .bits next => do
      let answer ← $ᵗ BitVec 256
      tests table cache (next answer)
  | cache, .coin n next => do
      let answer ← $ᵗ Fin (n + 1)
      tests table cache (next answer)

noncomputable def testExperiment (strategy : Strategy) (cache : QueryCache PointSpec) : ProbComp Nat := do
  let table ← $ᵗ PointTable
  tests (complete cache table) cache strategy

noncomputable def cost (strategy : Strategy) (cache : QueryCache PointSpec) : ENNReal :=
  expectedValue (testExperiment strategy cache) (fun n => (n : ENNReal))

private theorem expected_eq {α : Type} (first second : ProbComp α) (same : 𝒮[first] = 𝒮[second])
    (value : α → ENNReal) : expectedValue first value = expectedValue second value := by
  apply expectedValue_congr _ value
  intro output
  exact probOutput_congr rfl same

@[simp] theorem cost_done (cache : QueryCache PointSpec) : cost .done cache = 0 := by
  simp [cost, testExperiment, tests, expectedValue_const NeverFail.probFailure_eq_zero]

theorem cost_guess (cache : QueryCache PointSpec) (point : Point) (value : Digest) (next : Strategy) :
    cost (.guess point value next) cache = cost next cache + 1 := by
  simp only [cost, testExperiment, tests, expectedValue_bind, expectedValue_map, Nat.cast_add, Nat.cast_one,
    expectedValue_add, expectedValue_const NeverFail.probFailure_eq_zero]

theorem tests_reveal_fresh (cache : QueryCache PointSpec) (point : Point) (next : BitVec 256 → Strategy)
    (fresh : cache point = none) :
    𝒮[testExperiment (.reveal point next) cache] =
      𝒮[do let answer ← $ᵗ BitVec 256; testExperiment (next answer) (cache.cacheQuery point answer)] := by
  unfold testExperiment
  simp only [tests]
  rw [← uniform_update_bind point]
  simp only [complete_update cache _ point fresh, complete, fresh, Option.getD_none, Function.update_self]

theorem cost_reveal_fresh (cache : QueryCache PointSpec) (point : Point) (next : BitVec 256 → Strategy)
    (fresh : cache point = none) :
    cost (.reveal point next) cache = expectedValue ($ᵗ BitVec 256)
      (fun answer => cost (next answer) (cache.cacheQuery point answer)) := by
  rw [cost, expected_eq _ _ (tests_reveal_fresh cache point next fresh), expectedValue_bind]
  rfl

theorem cost_bits (cache : QueryCache PointSpec) (next : BitVec 256 → Strategy) :
    cost (.bits next) cache = expectedValue ($ᵗ BitVec 256) (fun answer => cost (next answer) cache) := by
  have same : 𝒮[testExperiment (.bits next) cache] =
      𝒮[do let answer ← $ᵗ BitVec 256; testExperiment (next answer) cache] := by
    unfold testExperiment
    simp only [tests]
    exact evalSPMF_bind_bind_swap _ _ _
  rw [cost, expected_eq _ _ same, expectedValue_bind]
  rfl

theorem cost_coin (cache : QueryCache PointSpec) (n : Nat) (next : Fin (n + 1) → Strategy) :
    cost (.coin n next) cache = expectedValue ($ᵗ Fin (n + 1)) (fun answer => cost (next answer) cache) := by
  have same : 𝒮[testExperiment (.coin n next) cache] =
      𝒮[do let answer ← $ᵗ Fin (n + 1); testExperiment (next answer) cache] := by
    unfold testExperiment
    simp only [tests]
    exact evalSPMF_bind_bind_swap _ _ _
  rw [cost, expected_eq _ _ same, expectedValue_bind]
  rfl

theorem cost_collision (cache : QueryCache PointSpec) (target : Digest) (next : BitVec 256 → Strategy) :
    cost (.collision target next) cache = expectedValue ($ᵗ BitVec 256)
      (fun answer => cost (next answer) cache) + 1 := by
  have same : testExperiment (.collision target next) cache =
      (fun n => n + 1) <$> testExperiment (.bits next) cache := by
    simp [testExperiment, tests]
  rw [cost, same, expectedValue_map]
  simp only [Nat.cast_add, Nat.cast_one, expectedValue_add,
    expectedValue_const NeverFail.probFailure_eq_zero]
  change cost (.bits next) cache + 1 = _
  rw [cost_bits]

noncomputable def fullExperiment (strategy : Strategy) (cache : QueryCache PointSpec) : ProbComp Bool := do
  let table ← $ᵗ PointTable
  playAll (complete cache table) cache strategy

noncomputable def risk (strategy : Strategy) (cache : QueryCache PointSpec) : ENNReal :=
  Pr[fun hit => hit = true | fullExperiment strategy cache]

@[simp] theorem risk_done (cache : QueryCache PointSpec) : risk .done cache = 0 := by
  simp [risk, fullExperiment, playAll]

theorem risk_reveal_fresh (cache : QueryCache PointSpec) (point : Point) (next : BitVec 256 → Strategy)
    (fresh : cache point = none) :
    risk (.reveal point next) cache = expectedValue ($ᵗ BitVec 256)
      (fun answer => risk (next answer) (cache.cacheQuery point answer)) := by
  have same : 𝒮[fullExperiment (.reveal point next) cache] =
      𝒮[do let answer ← $ᵗ BitVec 256; fullExperiment (next answer) (cache.cacheQuery point answer)] := by
    unfold fullExperiment
    simp only [playAll]
    rw [← uniform_update_bind point]
    simp only [complete_update cache _ point fresh, complete, fresh, Option.getD_none, Function.update_self]
  rw [risk, probEvent_def, same, ← probEvent_def, probEvent_bind_eq_expectedValue]
  rfl

theorem risk_bits (cache : QueryCache PointSpec) (next : BitVec 256 → Strategy) :
    risk (.bits next) cache = expectedValue ($ᵗ BitVec 256) (fun answer => risk (next answer) cache) := by
  have same : 𝒮[fullExperiment (.bits next) cache] =
      𝒮[do let answer ← $ᵗ BitVec 256; fullExperiment (next answer) cache] := by
    unfold fullExperiment
    simp only [playAll]
    exact evalSPMF_bind_bind_swap _ _ _
  rw [risk, probEvent_def, same, ← probEvent_def, probEvent_bind_eq_expectedValue]
  rfl

theorem risk_coin (cache : QueryCache PointSpec) (n : Nat) (next : Fin (n + 1) → Strategy) :
    risk (.coin n next) cache = expectedValue ($ᵗ Fin (n + 1)) (fun answer => risk (next answer) cache) := by
  have same : 𝒮[fullExperiment (.coin n next) cache] =
      𝒮[do let answer ← $ᵗ Fin (n + 1); fullExperiment (next answer) cache] := by
    unfold fullExperiment
    simp only [playAll]
    exact evalSPMF_bind_bind_swap _ _ _
  rw [risk, probEvent_def, same, ← probEvent_def, probEvent_bind_eq_expectedValue]
  rfl

theorem risk_guess_le (cache : QueryCache PointSpec) (point : Point) (value : Digest) (next : Strategy) :
    risk (.guess point value next) cache ≤ 1 / 2 ^ 128 + risk next cache := by
  have bound := passive_or_le ($ᵗ PointTable)
    (fun table => decide (cache point = none ∧ truncate (complete cache table point) = value))
    (fun table => playAll (complete cache table) cache next)
  refine le_trans ?_ (add_le_add (prob_guess_le cache point value) le_rfl)
  simpa only [risk, fullExperiment, playAll, decide_eq_true_eq] using bound

theorem risk_collision_le (cache : QueryCache PointSpec) (target : Digest) (next : BitVec 256 → Strategy) :
    risk (.collision target next) cache ≤ 1 / 2 ^ 128 +
      expectedValue ($ᵗ BitVec 256) (fun answer => risk (next answer) cache) := by
  have same : 𝒮[fullExperiment (.collision target next) cache] =
      𝒮[do
        let answer ← $ᵗ BitVec 256
        let later ← fullExperiment (next answer) cache
        pure (decide (truncate answer = target) || later)] := by
    unfold fullExperiment
    simp only [playAll, bind_assoc]
    exact evalSPMF_bind_bind_swap _ _ _
  rw [risk, probEvent_def, same, ← probEvent_def]
  have bound := passive_or_le ($ᵗ BitVec 256) (fun answer => decide (truncate answer = target))
    (fun answer => fullExperiment (next answer) cache)
  have first : Pr[fun answer : BitVec 256 => decide (truncate answer = target) = true | $ᵗ BitVec 256] =
      1 / 2 ^ 128 := by
    simpa only [decide_eq_true_eq, Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, truncate] using
      SecurityUniform.prob_extract_mem 128 128 ({target} : Finset Digest)
  simpa only [first, probEvent_bind_eq_expectedValue, risk] using bound

/-- Adaptive monitor failure is bounded by its actual expected test count. This
is the form needed to combine disjoint secret key, graph, nonce, and index query classes
without charging the same global H-call budget several times. -/
theorem risk_le_expected (strategy : Strategy) (cache : QueryCache PointSpec) :
    risk strategy cache ≤ cost strategy cache / 2 ^ 128 := by
  induction strategy generalizing cache with
  | done => simp
  | coin n next ih =>
    rw [risk_coin, cost_coin]
    calc
      _ ≤ expectedValue ($ᵗ Fin (n + 1)) (fun answer => cost (next answer) cache / 2 ^ 128) :=
        expectedValue_mono _ (fun answer => ih answer cache)
      _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]
  | bits next ih =>
    rw [risk_bits, cost_bits]
    calc
      _ ≤ expectedValue ($ᵗ BitVec 256) (fun answer => cost (next answer) cache / 2 ^ 128) :=
        expectedValue_mono _ (fun answer => ih answer cache)
      _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]
  | reveal point next ih =>
    cases present : cache point with
    | some answer =>
      simpa [risk, cost, fullExperiment, testExperiment, playAll, tests, complete, present,
        cacheQuery_same cache point answer present] using ih answer cache
    | none =>
      rw [risk_reveal_fresh cache point next present, cost_reveal_fresh cache point next present]
      calc
        _ ≤ expectedValue ($ᵗ BitVec 256) (fun answer => cost (next answer) (cache.cacheQuery point answer) / 2 ^ 128) :=
          expectedValue_mono _ (fun answer => ih answer (cache.cacheQuery point answer))
        _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]
  | guess point value next ih =>
    rw [cost_guess]
    calc
      _ ≤ 1 / 2 ^ 128 + risk next cache := risk_guess_le cache point value next
      _ ≤ 1 / 2 ^ 128 + cost next cache / 2 ^ 128 := add_le_add le_rfl (ih cache)
      _ = _ := by simp only [div_eq_mul_inv]; ring
  | collision target next ih =>
    rw [cost_collision]
    calc
      _ ≤ 1 / 2 ^ 128 + expectedValue ($ᵗ BitVec 256) (fun answer => risk (next answer) cache) :=
        risk_collision_le cache target next
      _ ≤ 1 / 2 ^ 128 + expectedValue ($ᵗ BitVec 256) (fun answer => cost (next answer) cache / 2 ^ 128) :=
        add_le_add le_rfl (expectedValue_mono _ (fun answer => ih answer cache))
      _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]; ring


end SigGolfCandidate.Hypertree.SecurityGraphPassiveCost
