import SigGolfCandidate.Hypertree.SecurityMonitorVerifyBudget

namespace SigGolfCandidate.Hypertree.SecurityMonitorResidual
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorCompose SecurityGraphMonitorNoContact
  SecurityGraphMonitorChainState SecurityGraphMonitorInvariant SecurityGraphMonitorPublicState
  SecurityGraphMonitorVerify SecurityGraphQuery SecurityGraphReference
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A clean residual cache also agrees with the public programmed oracle. -/
theorem agrees_public (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (base : Hash) (agree : cache.AgreesWithFn base) :
    cache.AgreesWithFn (programmed (privateTable factors) (labels factors) base) := by
  intro query answer present
  rw [locate_programmed]
  cases located : locate query with
  | none => exact agree present
  | some position =>
    dsimp only
    rw [if_neg (safe query answer present position located).1]
    exact agree present

/-- Sampling a residual query never changes an already cached answer. -/
theorem random_preserves (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((randomOracle (spec := HashSpec) query).run cache))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2 old = some value := by
  cases found : cache query with
  | some answer =>
    simp only [randomOracle.run_eq, found, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact present
  | none =>
    simp only [randomOracle.run_eq, found, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨answer, _, same⟩ := member
    cases same
    have different : old ≠ query := by intro equal; subst old; rw [found] at present; cases present
    simpa only [QueryCache.cacheQuery_of_ne _ _ different] using present

theorem random_present (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((randomOracle (spec := HashSpec) query).run cache)) :
    result.2 query = some result.1 := by
  cases found : cache query with
  | some answer =>
    simp only [randomOracle.run_eq, found, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact found
  | none =>
    simp only [randomOracle.run_eq, found, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨answer, _, same⟩ := member
    cases same
    exact QueryCache.cacheQuery_self ..

theorem query_preserves (factors : Factors) (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2 old = some value := by
  cases canonical : SecurityGraphOracle.canonical (privateTable factors) (labels factors) query with
  | some answer =>
    simp only [SecurityGraphOracle.publicOracle, canonical, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact present
  | none =>
    simp only [SecurityGraphOracle.publicOracle, canonical] at member
    exact random_preserves query cache result member old value present

/-- Every completed raw verifier preserves all earlier residual answers. -/
theorem completed_preserves {α : Type} (factors : Factors) (signed : Finset (BitVec 152))
    (program : OracleComp HashSpec α) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe factors signed exposed cache) (result : SecurityGraphMonitorVerify.Result α)
    (member : some result ∈ support (stopped factors.1 exposed (compile factors.2.2 program exposed cache)))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2.2 old = some value := by
  induction program using OracleComp.inductionOn generalizing exposed cache with
  | pure answer =>
    simp only [compile_pure, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact present
  | query_bind query next ih =>
    rw [compile_query, stopped_public_bind factors signed exposed cache initial, mem_support_bind_iff] at member
    obtain ⟨read, queried, tail⟩ := member
    cases read with
    | none => simp only [continueWith, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
    | some answer =>
      have spec := read_spec factors signed exposed cache initial query answer queried
      exact ih answer.1 answer.2.1 answer.2.2 (public_read_safe factors signed exposed cache initial query answer queried)
        tail (query_preserves factors query cache (answer.1,answer.2.2) spec.2.2.2 old value present)

/-- The first noncanonical query is present after any normally completed run. -/
theorem first_present {α : Type} (factors : Factors) (signed : Finset (BitVec 152))
    (query : Query) (next : BitVec 256 → OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (result : SecurityGraphMonitorVerify.Result α)
    (member : some result ∈ support (stopped factors.1 exposed
      (compile factors.2.2 (liftM (HashSpec.query query) >>= next) exposed cache)))
    (noncanonical : SecurityGraphOracle.canonical (privateTable factors) (labels factors) query = none) :
    result.2.2 query ≠ none := by
  rw [compile_query, stopped_public_bind factors signed exposed cache initial, mem_support_bind_iff] at member
  obtain ⟨read, queried, tail⟩ := member
  cases read with
  | none => simp only [continueWith, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
  | some answer =>
    have spec := read_spec factors signed exposed cache initial query answer queried
    have sampled := spec.2.2.2
    simp only [SecurityGraphOracle.publicOracle, noncanonical] at sampled
    have present := completed_preserves factors signed (next answer.1) answer.2.1 answer.2.2
      (public_read_safe factors signed exposed cache initial query answer queried) result tail query answer.1
      (random_present query cache _ sampled)
    rw [present]
    exact Option.some_ne_none _

/-- The actual verifier's H5 input remains cached for the extraction argument. -/
theorem verifier_index_present (factors : Factors) (signed : Finset (BitVec 152))
    (pk : PublicKey) (message : Message) (signature : SignatureEncoding.Compact)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (result : SecurityGraphMonitorVerify.Result Bool)
    (member : some result ∈ support (stopped factors.1 exposed
      (compile factors.2.2 (SecurityVerify.verifyCompact pk message signature) exposed cache))) :
    result.2.2 (SecurityRandomOracle.indexInput pk message signature.randomizer) ≠ none := by
  exact first_present factors signed (SecurityRandomOracle.indexInput pk message signature.randomizer) _
    exposed cache initial result member (SecurityGraphState.canonical_index _ _ pk message signature.randomizer)

#print axioms verifier_index_present
end SigGolfCandidate.Hypertree.SecurityMonitorResidual
