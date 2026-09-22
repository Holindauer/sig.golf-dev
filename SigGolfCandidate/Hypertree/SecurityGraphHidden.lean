import SigGolfCandidate.Hypertree.SecurityGraphUniform
import SigGolfCandidate.Hypertree.SecurityCache

namespace SigGolfCandidate.Hypertree.SecurityGraphHidden
open SigGolf OracleComp OracleSpec SecurityCache
set_option backward.isDefEq.respectTransparency false

noncomputable def observe {α : Type} (program : OracleComp World α) (cache : QueryCache HashSpec) :
    ProbComp α := (simulateQ implementation program).run' cache

theorem cacheQuery_comm (cache : QueryCache HashSpec) (first second : Query)
    (different : first ≠ second) (a b : BitVec 256) :
    (cache.cacheQuery first a).cacheQuery second b =
      (cache.cacheQuery second b).cacheQuery first a := by
  ext query
  by_cases one : query = first
  · subst query; simp [different]
  · by_cases two : query = second
    · subst query; simp [different.symm]
    · simp [QueryCache.cacheQuery_of_ne, one, two]

/-- Filling a single previously unseen hash cell with a uniform answer does not
change any later observable output. The continuation may query that cell, adapt
its queries, and use arbitrary private randomness. -/
theorem fill_fresh {α : Type} (program : OracleComp World α) (cache : QueryCache HashSpec)
    (input : Query) (fresh : cache input = none) :
    𝒮[do let answer ← $ᵗ BitVec 256; observe program (cache.cacheQuery input answer)] =
      𝒮[observe program cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value =>
    apply evalSPMF_ext
    intro output
    change Pr[= output | (do let _ ← $ᵗ BitVec 256; pure value)] = Pr[= output | (pure value : ProbComp α)]
    rw [probOutput_bind_const]
    simp
  | query_bind query next ih =>
    cases query with
    | inl coin =>
      have step (cache : QueryCache HashSpec) :
          observe (liftM (World.query (.inl coin)) >>= next) cache =
          (do let answer ← liftM (unifSpec.query coin); observe (next answer) cache) := by
        rw [observe, run'_query_bind]
        change ((fun answer => (answer, cache)) <$> (liftM (unifSpec.query coin) : ProbComp _) >>= _) = _
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, observe]
      simp_rw [step]
      rw [evalSPMF_bind_bind_swap]
      apply evalSPMF_bind_congr
      intro answer _
      exact ih answer cache fresh
    | inr query =>
      have step (cache : QueryCache HashSpec) :
          observe (liftM (World.query (.inr query)) >>= next) cache =
          (do let result ← (randomOracle (spec := HashSpec) query).run cache
              observe (next result.1) result.2) := by
        exact run'_query_bind (.inr query) next cache
      simp_rw [step]
      by_cases same : query = input
      · subst query
        simp only [randomOracle.run_eq, QueryCache.cacheQuery_self, pure_bind, fresh]
        simp only [bind_assoc, pure_bind]
      · cases present : cache query with
        | some value =>
          simp only [randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ same, present, pure_bind]
          exact ih value cache fresh
        | none =>
          simp only [randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ same, present,
            bind_assoc, pure_bind]
          rw [evalSPMF_bind_bind_swap]
          apply evalSPMF_bind_congr
          intro answer _
          simp_rw [cacheQuery_comm cache input query (Ne.symm same)]
          exact ih answer (cache.cacheQuery query answer)
            (by simpa only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm same)] using fresh)

/-- A hidden hash query may be inserted at any cache state without changing the
observable continuation's distribution. -/
theorem insert_query {α : Type} (program : OracleComp World α) (cache : QueryCache HashSpec)
    (input : Query) :
    𝒮[do
      let result ← (randomOracle (spec := HashSpec) input).run cache
      observe program result.2] = 𝒮[observe program cache] := by
  cases present : cache input with
  | some answer => simp only [randomOracle.run_eq, present, pure_bind]
  | none =>
    simp only [randomOracle.run_eq, present, bind_assoc, pure_bind]
    exact fill_fresh program cache input present

/-- Arbitrary hidden adaptive oracle precomputation may be inserted before an
observable continuation. Its output is discarded but its oracle cache is retained.
No finite bound on the hash-input domain is assumed. -/
theorem insert_prefix {α β : Type} (precomputation : OracleComp HashSpec α)
    (program : OracleComp World β) (cache : QueryCache HashSpec) :
    𝒮[do
      let result ← (simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)) precomputation).run cache
      observe program result.2] = 𝒮[observe program cache] := by
  induction precomputation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
    have step : (simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)) (liftM (HashSpec.query input) >>= next)).run cache =
        (do
          let result ← (randomOracle (spec := HashSpec) input).run cache
          (simulateQ (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp)) (next result.1)).run result.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [step]
    simp only [bind_assoc]
    calc
      _ = 𝒮[do
        let result ← (randomOracle (spec := HashSpec) input).run cache
        observe program result.2] := by
          apply evalSPMF_bind_congr
          intro result _
          exact ih result.1 result.2
      _ = _ := insert_query program cache input

/-- The actual shared lazy random oracle may equivalently start from independent
canonical graph labels and the exact graph cache. This identity preserves the
complete observable continuation, including its own hash counter when supplied
as part of its result; ghost precomputation is not charged as candidate execution. -/
theorem graph_presampling {α : Type} (privateAnswers : SecurityDerivation.Slot → BitVec 256)
    (program : OracleComp World α) (initial : SecurityGraph.Labels) :
    𝒮[observe program ∅] =
      𝒮[do
        let labels ← $ᵗ SecurityGraph.Labels
        observe program (SecurityGraphSampling.graphCache privateAnswers
          SecurityGraphOrder.positions labels ∅)] := by
  rw [← insert_prefix (SecurityGraph.readGraph privateAnswers SecurityGraphOrder.positions initial)
    program ∅]
  rw [evalSPMF_bind, SecurityGraphUniform.run_complete_graph]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]


end SigGolfCandidate.Hypertree.SecurityGraphHidden
