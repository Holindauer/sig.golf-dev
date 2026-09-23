import SigGolf.Security

namespace SigGolfCandidate.Hypertree.SecurityCache
open SigGolf OracleSpec OracleComp
set_option backward.isDefEq.respectTransparency false

/-- The same shared random oracle and forwarded private coins as the organizer's game. -/
noncomputable def implementation : QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

def hashBad (bad : Query → Prop) : World.Domain → Prop
  | .inl _ => False
  | .inr input => bad input

instance (bad : Query → Prop) [DecidablePred bad] : DecidablePred (hashBad bad) :=
  fun input => match input with
  | .inl _ => isFalse id
  | .inr input => inferInstanceAs (Decidable (bad input))

/-- Stop before a designated hash input; private-coin queries never trigger a stop. -/
noncomputable def stopBefore {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) : OracleComp World (Option α) :=
  OracleComp.construct (fun value => pure (some value))
    (fun input _ next => if hashBad bad input then pure none else do
      let answer ← liftM (World.query input)
      next answer) computation

@[simp] theorem stopBefore_pure {α : Type} (bad : Query → Prop) [DecidablePred bad] (x : α) :
    stopBefore bad (pure x) = pure (some x) := rfl

theorem stopBefore_query_bind {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (input : World.Domain) (next : World.Range input → OracleComp World α) :
    stopBefore bad (liftM (World.query input) >>= next) =
      (if hashBad bad input then pure none else do
        let answer ← liftM (World.query input)
        stopBefore bad (next answer)) := rfl

theorem run'_query_bind {α : Type} (input : World.Domain)
    (next : World.Range input → OracleComp World α) (cache : QueryCache HashSpec) :
    (simulateQ implementation (liftM (World.query input) >>= next)).run' cache =
      ((implementation input).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Caches may differ arbitrarily at designated secret inputs. -/
def AgreeOutside (bad : Query → Prop) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬bad input → left input = right input

theorem AgreeOutside.cacheQuery {bad : Query → Prop} {left right : QueryCache HashSpec}
    (agree : AgreeOutside bad left right) (input : Query) (answer : BitVec 256) :
    AgreeOutside bad (left.cacheQuery input answer) (right.cacheQuery input answer) := by
  intro other good
  by_cases same : other = input
  · subst other; simp
  · simpa only [QueryCache.cacheQuery_of_ne _ _ same] using agree other good

/-- Exact lazy-oracle simulation until the first designated input, allowing arbitrary
adaptive hash queries and private randomness. No distributional assumption about the
contents at secret inputs is needed. -/
theorem stopped_run_eq {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (left right : QueryCache HashSpec)
    (agree : AgreeOutside bad left right) :
    (simulateQ implementation (stopBefore bad computation)).run' left =
      (simulateQ implementation (stopBefore bad computation)).run' right := by
  induction computation using OracleComp.inductionOn generalizing left right with
  | pure value => simp
  | query_bind input next ih =>
    rw [stopBefore_query_bind]
    by_cases hit : hashBad bad input
    · simp [hit]
    · simp only [if_neg hit, run'_query_bind]
      cases input with
      | inl input =>
        dsimp [World] at next ih ⊢
        change ((fun answer => (answer, left)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _) =
          ((fun answer => (answer, right)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _)
        simp only [bind_map_left]
        apply bind_congr
        intro answer
        exact ih answer left right agree
      | inr input =>
        dsimp [World] at next ih ⊢
        change ((randomOracle (spec := HashSpec) input).run left >>= _) =
          ((randomOracle (spec := HashSpec) input).run right >>= _)
        have same := agree input hit
        cases hl : left input with
        | none =>
          have hr : right input = none := same.symm.trans hl
          rw [randomOracle.run_eq, hl, randomOracle.run_eq, hr]
          simp only [bind_assoc, pure_bind]
          apply bind_congr
          intro answer
          exact ih answer _ _ (agree.cacheQuery input answer)
        | some answer =>
          have hr : right input = some answer := same.symm.trans hl
          rw [randomOracle.run_eq, hl, randomOracle.run_eq, hr]
          simp only [pure_bind]
          exact ih answer left right agree

/-- Stopping can only remove successful executions. -/
theorem prob_stopped_le {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (stopBefore bad computation)).run' cache] ≤
        Pr[event | (simulateQ implementation computation).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
    rw [stopBefore_query_bind]
    split
    · simp
    · simp only [run'_query_bind, probEvent_bind_eq_tsum]
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

/-- The only successes lost by stopping are charged to the stop event itself. -/
theorem prob_le_stopped_add_stop {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[event | (simulateQ implementation computation).run' cache] ≤
      Pr[fun value => ∃ x, value = some x ∧ event x |
        (simulateQ implementation (stopBefore bad computation)).run' cache] +
      Pr[= none | (simulateQ implementation (stopBefore bad computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
    rw [stopBefore_query_bind]
    split
    · simp
    · simp only [run'_query_bind, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
        ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun result =>
        (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)

/-- Cache replacement costs only the chance of querying a differing input in the
replacement world. This is the cache-hybrid step for erasing secret key-dependent entries. -/
theorem prob_cache_change_le {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (left right : QueryCache HashSpec)
    (agree : AgreeOutside bad left right) (event : α → Prop) :
    Pr[event | (simulateQ implementation computation).run' left] ≤
      Pr[event | (simulateQ implementation computation).run' right] +
      Pr[= none | (simulateQ implementation (stopBefore bad computation)).run' right] := by
  have h := prob_le_stopped_add_stop bad computation left event
  rw [stopped_run_eq bad computation left right agree] at h
  exact h.trans (add_le_add (prob_stopped_le bad computation right event) le_rfl)

end SigGolfCandidate.Hypertree.SecurityCache
