import SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling
import SigGolfCandidate.Hypertree.SecurityGraphTraceContact

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphMonitorProgram
  SecurityGraphMonitorInvariant SecurityGraphMonitorCoupling SecurityGraphMonitorChainState
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorPublicState SecurityGraphTraceContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- A normally completed monitored call is an actual supported graph-oracle call,
with exactly the expected cache transition and neither first-contact flag. -/
theorem read_spec (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    ¬inputHit factors exposed query ∧ ¬outputHit factors query result.1 ∧
      result.2.1 = opened factors exposed query ∧
      (result.1, result.2.2) ∈ support
        ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache) := by
  rw [stopped_public_oracle _ _ _ _ _ initial.1 initial.2.2] at member
  by_cases first : inputHit factors exposed query
  · simp only [if_pos first, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
  · rw [if_neg first, mem_support_bind_iff] at member
    obtain ⟨answer, queried, after⟩ := member
    by_cases second : outputHit factors query answer.1
    · simp only [if_pos second, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at after
    · simp only [if_neg second, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at after
      subst result
      exact ⟨first, second, rfl, queried⟩

/-- The extraction's wrong-input target equality is exactly the output flag. -/
theorem collision_iff (factors : Factors) (hash : Hash) (query : Query) :
    CollisionContact factors hash query ↔ outputHit factors query (hash query) := by
  unfold CollisionContact outputHit
  cases located : locate query with
  | none => simp
  | some position => simp

/-- An unauthorized canonical predecessor is still hidden by the exposure
invariant, so the extraction's hidden-input contact triggers the input flag. -/
theorem hidden_implies_input (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (safe : ExposedSafe factors.2.2 signed exposed)
    (query : Query) (contact : HiddenContact factors signed query) : inputHit factors exposed query := by
  obtain ⟨address, step, unauthorized, equal⟩ := contact
  have hidden := safe.hidden factors.2.2 signed exposed (predecessor address step) unauthorized
  have canonical : query = (Position.chain address step).input (privateTable factors) (labels factors) := by
    rw [SecurityGraphMonitorCoupling.canonical_chain_input]
    exact equal
  have located := locate_input (privateTable factors) (labels factors) (.chain address step)
  rw [← canonical] at located
  simp only [inputHit, located]
  exact ⟨hidden, canonical⟩

/-- No contact in the actual verifier query-log sense can occur on a normally
completed public-monitor call. This is the deterministic extraction boundary. -/
theorem read_no_contact (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (result : Answer) (hash : Hash) (answer : hash query = result.1)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    ¬Contact factors signed hash query := by
  have spec := read_spec factors signed exposed cache initial query result member
  intro contact
  rcases contact with collision | hidden
  · have hit := (collision_iff factors hash query).mp collision
    rw [answer] at hit
    exact spec.2.1 hit
  · exact spec.1 (hidden_implies_input factors signed exposed initial.2.1 query hidden)

end SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact
