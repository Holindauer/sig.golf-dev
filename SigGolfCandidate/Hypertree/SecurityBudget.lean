import SigGolfCandidate.Hypertree.SecurityGameHop

namespace SigGolfCandidate.Hypertree.SecurityBudget
open SigGolf OracleComp OracleSpec SecurityGameHop SecuritySeparation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Every private derivation and public H call costs one; adversary coins are free. -/
def charge : GameWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- Stop before the first H call exceeding the global budget. The bound includes
honest key generation, signing, and final checking, through their same oracle port. -/
noncomputable def cutoff {α : Type} (program : OracleComp GameWorld α) :
    Nat → OracleComp GameWorld (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun query _ next budget => if charge query ≤ budget then do
      let answer ← liftM (GameWorld.query query)
      next answer (budget - charge query)
    else pure none) program

@[simp] theorem cutoff_pure {α : Type} (value : α) (budget : Nat) :
    cutoff (pure value) budget = pure (some value) := rfl

theorem cutoff_query_bind {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) (budget : Nat) :
    cutoff (liftM (GameWorld.query query) >>= next) budget =
      if charge query ≤ budget then do
        let answer ← liftM (GameWorld.query query)
        cutoff (next answer) (budget - charge query)
      else pure none := rfl

theorem prependPublic_length_le (query : GameWorld.Domain) (inputs : List Query) :
    (prependPublic query inputs).length ≤ inputs.length + charge query := by
  cases query with
  | inl n => simp [prependPublic, charge]
  | inr query =>
    cases query with
    | inl slot => simp [prependPublic, charge]
    | inr input => simp only [prependPublic, charge]; split <;> simp

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp)) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) (cache : σ) :
    (simulateQ implementation (liftM (GameWorld.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Arbitrary computations, including adaptive and potentially over-budget ones,
become structurally bounded after cutoff. No bound on the original strategy is assumed. -/
theorem cutoff_publicTraceBound {α : Type} (program : OracleComp GameWorld α)
    (cache : SplitCache) (budget : Nat) : PublicTraceBound (cutoff program budget) cache budget := by
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value => simp [PublicTraceBound]
  | query_bind query next ih =>
    rw [cutoff_query_bind]
    split
    next allowed =>
      intro result hr
      rw [tracePublic_query_bind, run'_query_bind, mem_support_bind_iff] at hr
      obtain ⟨step, _, hr⟩ := hr
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨tail, ht, rfl⟩ := hr
      have bound := ih step.1 step.2 (budget - charge query)
      have htail : tail.1.2.length ≤ budget - charge query := by
        apply bound
        rw [StateT.run'_eq, support_map, Set.mem_image]
        exact ⟨tail, ht, rfl⟩
      exact (prependPublic_length_le query tail.1.2).trans (by omega)
    next exhausted => simp [PublicTraceBound]

/-- Record the total number of actual H calls, including repeated cache hits. -/
def counted {α : Type} (program : OracleComp GameWorld α) : OracleComp GameWorld (α × Nat) :=
  OracleComp.construct (fun value => pure (value, 0))
    (fun query _ next => do
      let answer ← liftM (GameWorld.query query)
      let result ← next answer
      return (result.1, result.2 + charge query)) program

@[simp] theorem counted_pure {α : Type} (value : α) :
    counted (pure value) = pure (value, 0) := rfl

theorem counted_query_bind {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    counted (liftM (GameWorld.query query) >>= next) = (do
      let answer ← liftM (GameWorld.query query)
      let result ← counted (next answer)
      return (result.1, result.2 + charge query)) := rfl

/-- Exact finite-budget event equivalence, valid for every stateful probabilistic
oracle. It does not assume a worst-case query bound on the original computation. -/
theorem prob_cutoff_eq_counted {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp)) (program : OracleComp GameWorld α)
    (cache : σ) (budget : Nat) (event : α → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (cutoff program budget)).run' cache] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ implementation (counted program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value => simp
  | query_bind query next ih =>
    rw [cutoff_query_bind, counted_query_bind]
    by_cases allowed : charge query ≤ budget
    · rw [if_pos allowed, run'_query_bind, run'_query_bind]
      simp only [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro step
      rw [ih step.1 step.2 (budget - charge query)]
      congr 1
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def]
      apply probEvent_congr' _ rfl
      intro result _
      have arithmetic : result.1.2 ≤ budget - charge query ↔ result.1.2 + charge query ≤ budget := by omega
      exact and_congr_right fun _ => arithmetic
    · rw [if_neg allowed, run'_query_bind]
      have exceeded (count : Nat) : ¬count + charge query ≤ budget := by omega
      simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, exceeded]

/-- The secret key-erasure bound applies to any strategy after total-call cutoff; no
uniform query bound on an unbounded adversary is needed. -/
theorem prob_cutoff_real_le_ideal_add_secretKey {α : Type} (program : OracleComp GameWorld α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) (cutoff program budget)).run' ∅] ≤
      Pr[event | (simulateQ idealGameOracle (cutoff program budget)).run' (∅, ∅)] +
        budget / (2 : ENNReal) ^ 128 :=
  prob_real_le_ideal_add_secretKey (cutoff program budget) budget
    (cutoff_publicTraceBound program (∅, ∅) budget) event

/-- The quantitatively bounded game hop has the organizer's event shape:
a successful outcome together with total H calls at most `budget`, for arbitrary
adaptive computations. The ideal game's call count is retained as well. -/
theorem prob_counted_real_le_ideal_add_secretKey {α : Type} (program : OracleComp GameWorld α)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) (counted program)).run' ∅] ≤
      Pr[fun result => event result.1 ∧ result.2 ≤ budget |
        (simulateQ idealGameOracle (counted program)).run' (∅, ∅)] +
          budget / (2 : ENNReal) ^ 128 := by
  have h := prob_cutoff_real_le_ideal_add_secretKey program budget
    (fun value => ∃ x, value = some x ∧ event x)
  simpa only [probEvent_bind_eq_tsum, prob_cutoff_eq_counted] using h

end SigGolfCandidate.Hypertree.SecurityBudget
