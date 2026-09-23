import SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicState

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphPublicMonitor SecurityGraphMonitorProgram
  SecurityGraphMonitorCoupling SecurityGraphMonitorInvariant SecurityGraphMonitorMetadata
  SecurityGraphMonitorChainState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- First-contact predicates inspect the sampled graph only in the stopped
coupling. The operational passive compiler never branches on either predicate. -/
def inputHit (factors : Factors) (exposed : QueryCache PointSpec) (query : Query) : Prop :=
  match locate query with
  | some (.chain address step) => exposed (predecessor address step) = none ∧
      query = (Position.chain address step).input (privateTable factors) (labels factors)
  | _ => False

def outputHit (factors : Factors) (query : Query) (answer : BitVec 256) : Prop :=
  match locate query with
  | none => False
  | some position => query ≠ position.input (privateTable factors) (labels factors) ∧
      truncate answer = truncate (labels factors position)

noncomputable def opened (factors : Factors) (exposed : QueryCache PointSpec) (query : Query) :
    QueryCache PointSpec :=
  match locate query with
  | none => exposed
  | some (.chain address step) =>
      if query = (Position.chain address step).input (privateTable factors) (labels factors) then
        exposed.cacheQuery (successor address step) (factors.1 (successor address step))
      else exposed
  | some position => revealCache factors.1 (required position) exposed

/-- Exact stopped coupling of one public call through the actual explicit graph
oracle, retaining the arbitrary continuation and both caches. -/
theorem stopped_public_oracle {α : Type} (factors : Factors) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree factors.1 exposed) (clean : ResidualSafe factors cache) :
    stopped factors.1 exposed (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query next) =
      (if inputHit factors exposed query then pure none else do
        let result ← (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache
        if outputHit factors query result.1 then pure none
        else (stopped factors.1 (opened factors exposed query)
          (next result.1 (opened factors exposed query) result.2))) := by
  cases located : locate query with
  | none =>
    simp only [inputHit, outputHit, opened, located, if_false]
    exact stopped_public_outside _ factors.2.1 _ _ _ _ _ located
  | some position =>
    cases position with
    | chain address step =>
      have dispatch : SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query next =
          SecurityGraphMonitorOracle.chainStep exposed cache address step query next := by
        simp only [SecurityGraphMonitorOracle.publicStep, located]
      rw [dispatch, stopped_chain _ _ _ _ _ _ _ agree (clean.chain factors cache query address step located)]
      have payload := canonical_chain_input factors address step
      unfold chainStopped
      simp only [inputHit, outputHit, opened, SecurityGraphOracle.publicOracle,
        SecurityGraphOracle.canonical, located, payload]
      by_cases canonical : query = SecurityGraphContact.chainInput address step
          (truncate (factors.1 (predecessor address step)))
      · by_cases hidden : exposed (predecessor address step) = none
        · simp only [canonical, hidden, true_and, and_true, if_true]
        · simp only [canonical, hidden, false_and, if_false, if_true, not_true_eq_false,
            StateT.run_pure, pure_bind]
          simp only [ne_eq, not_true_eq_false, eq_self, false_and, if_false]
          rfl
      · simp only [canonical, and_false, if_false, not_false_eq_true, true_and]
        simp only [ne_eq, canonical, not_false_eq_true, true_and]
        rfl
    | leaf level tree side =>
      have localClean : CacheMissTarget cache query (truncate (labels factors (.leaf level tree side))) :=
        fun answer present => (clean query answer present _ located).2
      rw [stopped_public_nonchain_oracle _ factors.2.1 _ _ _ _ _ _ located
        (by intros; intro h; cases h) localClean]
      simp only [inputHit, outputHit, opened, located, if_false]
    | node level tree =>
      have localClean : CacheMissTarget cache query (truncate (labels factors (.node level tree))) :=
        fun answer present => (clean query answer present _ located).2
      rw [stopped_public_nonchain_oracle _ factors.2.1 _ _ _ _ _ _ located
        (by intros; intro h; cases h) localClean]
      simp only [inputHit, outputHit, opened, located, if_false]

end SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling
