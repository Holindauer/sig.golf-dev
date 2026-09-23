import SigGolfCandidate.Hypertree.SecuritySeparation

namespace SigGolfCandidate.Hypertree.SecurityGameHop
open SigGolf OracleComp OracleSpec SecurityDerivation SecuritySecretKey SecuritySeparation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Private coins, private derivation requests, and public random-oracle queries. -/
abbrev GameWorld := unifSpec + SplitWorld

noncomputable def coins {σ : Type} : QueryImpl unifSpec (StateT σ ProbComp) :=
  fun n => StateT.mk fun cache => (fun answer => (answer, cache)) <$>
    (liftM (unifSpec.query n) : ProbComp _)

noncomputable def realGameOracle (secretKey : SecretKey) :
    QueryImpl GameWorld (StateT (QueryCache HashSpec) ProbComp) := coins (σ := QueryCache HashSpec) + realOracle secretKey

noncomputable def idealGameOracle : QueryImpl GameWorld (StateT SplitCache ProbComp) :=
  coins (σ := SplitCache) + idealOracle

def isBad (secretKey : SecretKey) : GameWorld.Domain → Prop
  | .inl _ => False
  | .inr query => publicSecretKeyHit secretKey query

noncomputable def stop {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) :
    OracleComp GameWorld (Option α) :=
  OracleComp.construct (fun value => pure (some value))
    (fun query _ next => if isBad secretKey query then pure none else do
      let answer ← liftM (GameWorld.query query)
      next answer) program

@[simp] theorem stop_pure {α : Type} (secretKey : SecretKey) (value : α) :
    stop secretKey (pure value) = pure (some value) := rfl

theorem stop_query_bind {α : Type} (secretKey : SecretKey) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    stop secretKey (liftM (GameWorld.query query) >>= next) =
      (if isBad secretKey query then pure none else do
        let answer ← liftM (GameWorld.query query)
        stop secretKey (next answer)) := rfl

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp)) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) (cache : σ) :
    (simulateQ implementation (liftM (GameWorld.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- The exact private/public cache coupling also preserves every private-coin draw,
including arbitrary uniform ranges chosen adaptively by the adversary. -/
theorem stopped_separation {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (real : QueryCache HashSpec) (ideal : SplitCache) (related : Related secretKey real ideal) :
    (simulateQ (realGameOracle secretKey) (stop secretKey program)).run' real =
      (simulateQ idealGameOracle (stop secretKey program)).run' ideal := by
  induction program using OracleComp.inductionOn generalizing real ideal with
  | pure value => simp
  | query_bind query next ih =>
    rw [stop_query_bind]
    by_cases hit : isBad secretKey query
    · simp [hit]
    · simp only [if_neg hit, run'_query_bind]
      cases query with
      | inl n =>
        dsimp [GameWorld] at next ih ⊢
        change ((fun answer => (answer, real)) <$> (liftM (unifSpec.query n) : ProbComp _) >>= _) =
          ((fun answer => (answer, ideal)) <$> (liftM (unifSpec.query n) : ProbComp _) >>= _)
        simp only [bind_map_left]
        apply bind_congr
        intro answer
        exact ih answer real ideal related
      | inr query =>
        change ((realOracle secretKey query).run real >>= _) = ((idealOracle query).run ideal >>= _)
        exact couple_query_good secretKey query real ideal related hit _ _ ih

noncomputable def prependPublic (query : GameWorld.Domain) (inputs : List Query) : List Query :=
  match query with
  | .inl _ => inputs
  | .inr (.inl _) => inputs
  | .inr (.inr input) => if SecretKeyEligible input then input :: inputs else inputs

noncomputable def tracePublic {α : Type} (program : OracleComp GameWorld α) :
    OracleComp GameWorld (α × List Query) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← liftM (GameWorld.query query)
      let result ← next answer
      return (result.1, prependPublic query result.2)) program

@[simp] theorem tracePublic_pure {α : Type} (value : α) :
    tracePublic (pure value) = pure (value, []) := rfl

theorem tracePublic_query_bind {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    tracePublic (liftM (GameWorld.query query) >>= next) = (do
      let answer ← liftM (GameWorld.query query)
      let result ← tracePublic (next answer)
      return (result.1, prependPublic query result.2)) := rfl

theorem hit_prepend (secretKey : SecretKey) (query : GameWorld.Domain) (inputs : List Query) :
    SecretKeyHitTrace (prependPublic query inputs) secretKey ↔
      isBad secretKey query ∨ SecretKeyHitTrace inputs secretKey := by
  cases query with
  | inl n => simp [prependPublic, isBad]
  | inr query =>
    cases query with
    | inl slot => simp [prependPublic, isBad, publicSecretKeyHit]
    | inr input =>
      by_cases eligible : SecretKeyEligible input <;>
        simp [prependPublic, isBad, publicSecretKeyHit, eligible, SecretKeyHitTrace]

/-- In the independent world, the secret key monitor reads the secret key-eligible public-query log. -/
theorem prob_stop_eq_trace {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (cache : SplitCache) :
    Pr[= none | (simulateQ idealGameOracle (stop secretKey program)).run' cache] =
      Pr[fun result => SecretKeyHitTrace result.2 secretKey |
        (simulateQ idealGameOracle (tracePublic program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [SecretKeyHitTrace]
  | query_bind query next ih =>
    rw [stop_query_bind, tracePublic_query_bind]
    by_cases hit : isBad secretKey query
    · rw [if_pos hit, run'_query_bind]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, hit_prepend, hit, true_or,
        probEvent_const, NeverFail.probFailure_eq_zero, tsub_zero,
        simulateQ_pure, StateT.run_pure, map_pure, probOutput_pure, ite_true,
        probEvent_bind_of_const, one_mul]
    · rw [if_neg hit, run'_query_bind, run'_query_bind]
      simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro result
      rw [ih result.1 result.2]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, hit_prepend, hit, false_or]

/-- The private oracle may be queried arbitrarily; `limit` bounds only public H
queries in the private-derivation domains. Public chain/node/index calls are excluded
from this count, so the main secret key and target query classes can share one budget. -/
def PublicTraceBound {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) (limit : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ idealGameOracle (tracePublic program)).run' cache),
    result.2.length ≤ limit

/-- Expected number of secret key-eligible public queries in the independent game.
Keeping this quantity, rather than replacing it by Q, permits shared-budget composition. -/
noncomputable def expectedSecretKeyQueries {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) : ENNReal :=
  ∑' result, Pr[= result | (simulateQ idealGameOracle (tracePublic program)).run' cache] *
    (result.2.length : ENNReal)

theorem prob_stop_secretKey_le_expected {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) :
    Pr[= none | sampleSecretKey >>= fun secretKey =>
      (simulateQ idealGameOracle (stop secretKey program)).run' cache] ≤
        expectedSecretKeyQueries program cache / (2 : ENNReal) ^ 128 := by
  let trace := (simulateQ idealGameOracle (tracePublic program)).run' cache
  calc
    _ = Pr[= true | sampleSecretKey >>= fun secretKey =>
        (fun result => decide (SecretKeyHitTrace result.2 secretKey)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, prob_stop_eq_trace, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun secretKey => decide (SecretKeyHitTrace result.2 secretKey)) <$> sampleSecretKey] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ ∑' result, Pr[= result | trace] * ((result.2.length : ENNReal) / 2 ^ 128) := by
      simp only [probOutput_bind_eq_tsum, probOutput_map, decide_eq_true_eq]
      exact ENNReal.tsum_le_tsum fun result =>
        mul_le_mul' le_rfl (prob_secretKeyHitTrace_le result.2)
    _ = _ := by
      simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
      rfl

theorem prob_stop_secretKey_le {α : Type} (program : OracleComp GameWorld α) (cache : SplitCache)
    (limit : Nat) (bounded : PublicTraceBound program cache limit) :
    Pr[= none | sampleSecretKey >>= fun secretKey =>
      (simulateQ idealGameOracle (stop secretKey program)).run' cache] ≤ limit / (2 : ENNReal) ^ 128 := by
  let trace := (simulateQ idealGameOracle (tracePublic program)).run' cache
  calc
    _ = Pr[= true | sampleSecretKey >>= fun secretKey =>
        (fun result => decide (SecretKeyHitTrace result.2 secretKey)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, prob_stop_eq_trace, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun secretKey => decide (SecretKeyHitTrace result.2 secretKey)) <$> sampleSecretKey] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hr
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (prob_secretKeyHitTrace_le result.2).trans
        (ENNReal.div_le_div (by exact_mod_cast bounded result hr) le_rfl)

private theorem prob_stopped_le {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp)) (secretKey : SecretKey)
    (program : OracleComp GameWorld α) (cache : σ) (event : α → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (stop secretKey program)).run' cache] ≤
        Pr[event | (simulateQ implementation program).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
    rw [stop_query_bind]
    split
    · simp
    · simp only [run'_query_bind, probEvent_bind_eq_tsum]
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

private theorem prob_le_stopped_add_stop {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp)) (secretKey : SecretKey)
    (program : OracleComp GameWorld α) (cache : σ) (event : α → Prop) :
    Pr[event | (simulateQ implementation program).run' cache] ≤
      Pr[fun value => ∃ x, value = some x ∧ event x |
        (simulateQ implementation (stop secretKey program)).run' cache] +
      Pr[= none | (simulateQ implementation (stop secretKey program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
    rw [stop_query_bind]
    split
    · simp
    · simp only [run'_query_bind, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
        ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun result =>
        (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)

/-- Quantitative real-to-independent-private game hop for arbitrary adaptive
programs and private coins, using the candidate's exact chain/nonce input map.
No secret key-dependent cache independence premise remains at the empty starting state. -/
theorem prob_real_le_ideal_add_secretKey {α : Type} (program : OracleComp GameWorld α)
    (limit : Nat) (bounded : PublicTraceBound program (∅, ∅) limit) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
      Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)] + limit / (2 : ENNReal) ^ 128 := by
  have compare (secretKey : SecretKey) :
      Pr[event | (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
        Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)] +
        Pr[= none | (simulateQ idealGameOracle (stop secretKey program)).run' (∅, ∅)] := by
    have h := prob_le_stopped_add_stop (realGameOracle secretKey) secretKey program ∅ event
    rw [stopped_separation secretKey program ∅ (∅, ∅) (by constructor <;> intros <;> rfl)] at h
    exact h.trans (add_le_add (prob_stopped_le idealGameOracle secretKey program (∅, ∅) event) le_rfl)
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
        (simulateQ idealGameOracle program).run' (∅, ∅)] +
        Pr[= none | sampleSecretKey >>= fun secretKey =>
          (simulateQ idealGameOracle (stop secretKey program)).run' (∅, ∅)] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (compare secretKey)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa using add_le_add
        (le_refl (Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)]))
        (prob_stop_secretKey_le program (∅, ∅) limit bounded)

/-- Sharp secret key-erasure penalty for composition with disjoint target-query costs. -/
theorem prob_real_le_ideal_add_expected_secretKey {α : Type} (program : OracleComp GameWorld α)
    (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
      Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)] + expectedSecretKeyQueries program (∅, ∅) / (2 : ENNReal) ^ 128 := by
  have compare (secretKey : SecretKey) :
      Pr[event | (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
        Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)] +
        Pr[= none | (simulateQ idealGameOracle (stop secretKey program)).run' (∅, ∅)] := by
    have h := prob_le_stopped_add_stop (realGameOracle secretKey) secretKey program ∅ event
    rw [stopped_separation secretKey program ∅ (∅, ∅) (by constructor <;> intros <;> rfl)] at h
    exact h.trans (add_le_add (prob_stopped_le idealGameOracle secretKey program (∅, ∅) event) le_rfl)
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
        (simulateQ idealGameOracle program).run' (∅, ∅)] +
        Pr[= none | sampleSecretKey >>= fun secretKey =>
          (simulateQ idealGameOracle (stop secretKey program)).run' (∅, ∅)] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (compare secretKey)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa using add_le_add
        (le_refl (Pr[event | (simulateQ idealGameOracle program).run' (∅, ∅)]))
        (prob_stop_secretKey_le_expected program (∅, ∅))

end SigGolfCandidate.Hypertree.SecurityGameHop
