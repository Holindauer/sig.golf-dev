import SigGolfCandidate.Hypertree.SecurityGraphQuery

namespace SigGolfCandidate.Hypertree.SecurityGraphOracle
open SigGolf OracleComp OracleSpec SecurityDerivation SecurityGraph SecurityGraphSampling SecurityGraphOrder
  SecurityGraphQuery SecurityCache
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Public graph queries return their pre-sampled label; every other query uses the residual oracle. -/
noncomputable def canonical (privateAnswers : Slot → BitVec 256) (labels : Labels) (query : Query) :
    Option (BitVec 256) :=
  match locate query with
  | none => none
  | some position => if query = position.input privateAnswers labels then some (labels position) else none

noncomputable def embed (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : QueryCache HashSpec) : QueryCache HashSpec := graphCache privateAnswers positions labels residual

theorem canonical_eq_cache (privateAnswers : Slot → BitVec 256) (labels : Labels) (query : Query) :
    canonical privateAnswers labels query = graphCache privateAnswers positions labels ∅ query :=
  (complete_cache_lookup privateAnswers labels query).symm

/-- The canonical graph takes priority over any entries in the residual cache. -/
theorem embed_lookup (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : QueryCache HashSpec) (query : Query) :
    embed privateAnswers labels residual query =
      match canonical privateAnswers labels query with
      | some answer => some answer
      | none => residual query := by
  rw [canonical_eq_cache]
  by_cases found : ∃ position : Position, query = position.input privateAnswers labels
  · obtain ⟨position, same⟩ := found
    rw [same, embed, graphCache_inside privateAnswers positions labels residual position (positions_complete position),
      graphCache_inside privateAnswers positions labels ∅ position (positions_complete position)]
  · have outside : ∀ position ∈ positions, query ≠ position.input privateAnswers labels :=
      fun position _ same => found ⟨position, same⟩
    rw [embed, graphCache_outside privateAnswers positions labels residual query outside,
      graphCache_outside privateAnswers positions labels ∅ query outside]
    rfl

/-- Filling a noncanonical cell commutes with the embedding of the entire fixed graph. -/
theorem embed_cacheQuery (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : QueryCache HashSpec) (query : Query) (answer : BitVec 256)
    (outside : canonical privateAnswers labels query = none) :
    embed privateAnswers labels (residual.cacheQuery query answer) =
      (embed privateAnswers labels residual).cacheQuery query answer := by
  ext other
  by_cases same : other = query
  · subst other
    rw [embed_lookup, outside, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [embed_lookup, QueryCache.cacheQuery_of_ne _ _ same, QueryCache.cacheQuery_of_ne _ _ same, embed_lookup]

noncomputable def publicOracle (privateAnswers : Slot → BitVec 256) (labels : Labels) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  fun query => match canonical privateAnswers labels query with
  | some answer => pure answer
  | none => randomOracle query

/-- Exact one-query simulation, retaining the relation between the resulting cache states. -/
theorem query_run (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : QueryCache HashSpec) (query : Query) :
    (randomOracle (spec := HashSpec) query).run (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (publicOracle privateAnswers labels query).run residual := by
  cases graph : canonical privateAnswers labels query with
  | some answer =>
    simp only [randomOracle.run_eq, embed_lookup, graph, publicOracle, StateT.run_pure, map_pure]
  | none =>
    simp only [randomOracle.run_eq, embed_lookup, graph, publicOracle]
    cases cached : residual query with
    | some answer => simp only [map_pure]
    | none =>
      simp only [map_bind, map_pure]
      apply bind_congr
      intro answer
      rw [embed_cacheQuery privateAnswers labels residual query answer graph]

/-- The organizer's private coins pass through unchanged. -/
noncomputable def implementation (privateAnswers : Slot → BitVec 256) (labels : Labels) :
    QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + publicOracle privateAnswers labels

theorem world_query_run (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : QueryCache HashSpec) (query : World.Domain) :
    (SecurityCache.implementation query).run (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (implementation privateAnswers labels query).run residual := by
  cases query with
  | inl coin =>
    change ((fun answer => (answer, embed privateAnswers labels residual)) <$>
      (liftM (unifSpec.query coin) : ProbComp _)) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        ((fun answer => (answer, residual)) <$> (liftM (unifSpec.query coin) : ProbComp _))
    rw [Functor.map_map]
  | inr input => exact query_run privateAnswers labels residual input

/-- The explicit graph oracle simulates every adaptive program, including private coin queries. -/
theorem simulate_run (privateAnswers : Slot → BitVec 256) (labels : Labels)
    {α : Type} (program : OracleComp World α) (residual : QueryCache HashSpec) :
    (simulateQ SecurityCache.implementation program).run (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (simulateQ (implementation privateAnswers labels) program).run residual := by
  induction program using OracleComp.inductionOn generalizing residual with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, world_query_run, bind_map_left, map_bind]
    apply bind_congr
    intro result
    exact ih result.1 result.2

/-- Forgetting the residual cache gives exactly the observable public-graph experiment. -/
theorem observe_eq (privateAnswers : Slot → BitVec 256) (labels : Labels)
    {α : Type} (program : OracleComp World α) (residual : QueryCache HashSpec) :
    SecurityGraphHidden.observe program (embed privateAnswers labels residual) =
      (simulateQ (implementation privateAnswers labels) program).run' residual := by
  rw [SecurityGraphHidden.observe, StateT.run'_eq, simulate_run, Functor.map_map]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphOracle.observe_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms observe_eq

end SigGolfCandidate.Hypertree.SecurityGraphOracle
