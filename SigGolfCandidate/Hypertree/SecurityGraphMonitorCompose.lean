import SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorCompose
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram SecurityGraphMonitorChainState SecurityGraphMonitorPublicCoupling
  SecurityGraphMonitorNoContact SecurityGraphReference SecurityGraphQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def continueWith {α : Type} (table : PointTable)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    Option Answer → ProbComp (Option α)
  | none => pure none
  | some result => stopped table result.2.1 (next result.1 result.2.1 result.2.2)

/-- The stopped handler composes exactly as one monitored read followed by the
continuation; the returned exposure cache is the actual interpreter cache. -/
theorem stopped_public_bind {α : Type} (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    stopped factors.1 exposed (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query next) =
      (stopped factors.1 exposed (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))) >>= continueWith factors.1 next) := by
  rw [stopped_public_oracle _ _ _ _ _ initial.1 initial.2.2,
    stopped_public_oracle _ _ _ _ _ initial.1 initial.2.2]
  by_cases first : inputHit factors exposed query
  · simp only [if_pos first, pure_bind, continueWith]
  · simp only [if_neg first, bind_assoc]
    apply bind_congr
    intro result
    by_cases second : outputHit factors query result.1
    · simp only [if_pos second, pure_bind, continueWith]
    · simp only [if_neg second, stopped, pure_bind, continueWith]

/-- Extending the final residual cache reproduces the exact public graph answer
and also extends the earlier cache. Canonical planted cells take graph priority. -/
theorem query_support_agrees (factors : Factors) (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache))
    (base : Hash) (agree : result.2.AgreesWithFn base) :
    cache.AgreesWithFn base ∧ programmed (privateTable factors) (labels factors) base query = result.1 := by
  have oracleValue : programmed (privateTable factors) (labels factors) base query =
      (SecurityGraphOracle.canonical (privateTable factors) (labels factors) query).getD (base query) := by
    rw [locate_programmed]
    unfold SecurityGraphOracle.canonical
    cases locate query with
    | none => rfl
    | some position =>
      dsimp only
      split <;> rfl
  rw [oracleValue]
  cases canonical : SecurityGraphOracle.canonical (privateTable factors) (labels factors) query with
  | some value =>
    simp only [SecurityGraphOracle.publicOracle, canonical, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at member
    subst result
    exact ⟨agree, rfl⟩
  | none =>
    simp only [SecurityGraphOracle.publicOracle, canonical] at member
    cases present : cache query with
    | some value =>
      simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact ⟨agree, agree present⟩
    | none =>
      simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
      obtain ⟨value, _, equal⟩ := member
      cases equal
      exact (QueryCache.agreesWithFn_cacheQuery_iff cache query value base present).mp agree

end SigGolfCandidate.Hypertree.SecurityGraphMonitorCompose
