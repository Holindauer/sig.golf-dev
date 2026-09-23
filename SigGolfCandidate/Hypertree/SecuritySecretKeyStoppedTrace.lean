import SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
open SigGolf OracleComp OracleComp.EvalDist OracleSpec SecuritySecretKey SecurityDerivation
  SecuritySeparation SecurityGameHop SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def keep {α : Type} (secretKey : SecretKey) (result : α × List Query) : Option α :=
  if SecretKeyHitTrace result.2 secretKey then none else some result.1

private theorem run_query {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (input : GameWorld.Domain) (next : GameWorld.Range input → OracleComp GameWorld α) (cache : σ) :
    (simulateQ implementation (liftM (GameWorld.query input) >>= next)).run' cache =
      ((implementation input).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

private theorem run_map {σ α β : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (f : α → β) (cache : σ) :
    (simulateQ implementation (f <$> program)).run' cache =
      f <$> (simulateQ implementation program).run' cache := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

private theorem map_const {α β : Type} (program : ProbComp α) (value : β) :
    𝒮[(fun _ => value) <$> program] = 𝒮[(pure value : ProbComp β)] := by
  classical
  let : DecidableEq β := Classical.decEq β
  apply evalSPMF_ext
  intro output
  simp only [map_eq_pure_bind, probOutput_bind_const]
  simp

/-- Stopping before a secret key guess is exactly forgetting secret key-hit outcomes of the
full passive trace. The retained output can contain all other counters/results. -/
theorem stopped_eq_trace {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (secretKey : SecretKey) (program : OracleComp GameWorld α) (cache : σ) :
    𝒮[(simulateQ implementation (stop secretKey program)).run' cache] =
      𝒮[keep secretKey <$> (simulateQ implementation (tracePublic program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [keep, SecretKeyHitTrace]
  | query_bind input next ih =>
    rw [stop_query_bind, tracePublic_query_bind]
    by_cases hit : isBad secretKey input
    · rw [if_pos hit, run_query]
      simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
      have constant : (fun result : α × List Query => keep secretKey (result.1, prependPublic input result.2)) =
          fun _ => (none : Option α) := by
        funext result
        simp only [keep, hit_prepend, hit, true_or, if_true]
      rw [constant]
      simpa only [map_bind, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure] using (map_const
        ((implementation input).run cache >>= fun result =>
          (simulateQ implementation (tracePublic (next result.1))).run' result.2)
        (none : Option α)).symm
    · rw [if_neg hit, run_query, run_query]
      simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
      apply evalSPMF_bind_congr
      intro result _
      rw [ih result.1 result.2]
      congr 1
      congr 1
      funext tail
      simp only [keep, hit_prepend, hit, false_or]

/-- Logging secret key-eligible public inputs leaves the actual output unchanged. -/
theorem trace_output {α : Type} (program : OracleComp GameWorld α) :
    Prod.fst <$> tracePublic program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rw [tracePublic_query_bind]
    simp only [map_bind, bind_pure_comp, Functor.map_map]
    exact bind_congr ih

theorem run_trace_output {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (cache : σ) :
    Prod.fst <$> (simulateQ implementation (tracePublic program)).run' cache =
      (simulateQ implementation program).run' cache := by
  rw [←run_map, trace_output]

/-- A successful real run is included in a single ideal-world union event:
the same result succeeds, or its passive secret key trace hits. No expected cost is
transferred between games and no separate additive secret key penalty is introduced. -/
theorem real_le_ideal_union {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) (event : α → Prop) :
    Pr[event | (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
      Pr[fun result => event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
        (simulateQ idealGameOracle (tracePublic program)).run' (∅, ∅)] := by
  let lifted : Option α → Prop := fun value => match value with | none => True | some value => event value
  have same : 𝒮[keep secretKey <$> (simulateQ (realGameOracle secretKey) (tracePublic program)).run' ∅] =
      𝒮[keep secretKey <$> (simulateQ idealGameOracle (tracePublic program)).run' (∅, ∅)] := by
    rw [←stopped_eq_trace, ←stopped_eq_trace,
      SecurityGameHop.stopped_separation secretKey program ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  have events := probEvent_congr' (p := lifted) (q := lifted) (fun _ _ => Iff.rfl) same
  rw [probEvent_map, probEvent_map] at events
  have keep_event (result : α × List Query) : lifted (keep secretKey result) ↔ event result.1 ∨ SecretKeyHitTrace result.2 secretKey := by
    simp only [keep]
    split <;> simp_all [lifted]
  simp_rw [Function.comp_def, keep_event] at events
  rw [←events, ←run_trace_output (realGameOracle secretKey) program ∅, probEvent_map]
  exact probEvent_mono (fun _ _ h => Or.inl h)

/-- The union coupling applies directly to the organizer's total-call cutoff,
including executions which exhaust the budget during an honest block. -/
theorem real_cutoff_le_ideal_union {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | (simulateQ (realGameOracle secretKey) (cutoff program budget)).run' ∅] ≤
      Pr[fun result => event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
        (simulateQ idealGameOracle (tracePublic (cutoff program budget))).run' (∅, ∅)] :=
  real_le_ideal_union secretKey (cutoff program budget) event

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace.real_cutoff_le_ideal_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_cutoff_le_ideal_union
end SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
