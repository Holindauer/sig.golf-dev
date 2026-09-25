import SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorChainState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphMonitorProgram
  SecurityGraphMonitorCoupling SecurityGraphMonitorInvariant SecurityGraphContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

abbrev Answer := BitVec 256 × QueryCache PointSpec × QueryCache HashSpec

def Safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) : Prop :=
  Agree factors.1 exposed ∧ ExposedSafe factors.2.2 signed exposed ∧ ResidualSafe factors cache

theorem residual_insert (factors : Factors) (cache : QueryCache HashSpec) (safe : ResidualSafe factors cache)
    (query : Query) (answer : BitVec 256) (position : Position) (located : locate query = some position)
    (different : query ≠ position.input (privateTable factors) (labels factors))
    (miss : truncate answer ≠ truncate (labels factors position)) :
    ResidualSafe factors (cache.cacheQuery query answer) := by
  apply safe.cacheQuery factors cache query answer
  intro other otherLocated
  have same : position = other := Option.some.inj (located.symm.trans otherLocated)
  subst other
  exact ⟨different, miss⟩

/-- A completed noncanonical lookup retains the invariant only if the target
comparison missed. This includes both fresh draws and previously cached answers. -/
theorem residual_read_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (position : Position) (located : locate query = some position)
    (different : query ≠ position.input (privateTable factors) (labels factors)) (result : Answer)
    (member : some result ∈ support (do
      let output ← (randomOracle (spec := HashSpec) query).run cache
      if truncate output.1 = truncate (labels factors position) then pure none
      else pure (some (output.1, exposed, output.2)))) :
    Safe factors signed result.2.1 result.2.2 ∧
      truncate result.1 ≠ truncate (labels factors position) := by
  cases present : cache query with
  | some answer =>
    have miss := (initial.2.2 query answer present position located).2
    simp only [randomOracle.run_eq, present, pure_bind, if_neg miss, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact ⟨initial, miss⟩
  | none =>
    simp only [randomOracle.run_eq, present, bind_assoc, pure_bind, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    by_cases hit : truncate answer = truncate (labels factors position)
    · simp only [if_pos hit, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
    · simp only [if_neg hit, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact ⟨⟨initial.1, initial.2.1,
        residual_insert factors cache initial.2.2 query answer position located different hit⟩, hit⟩

/-- On a completed chain query, canonical input implies an authorized predecessor;
noncanonical input implies a noncollision with that fixed graph target. -/
def ChainClean (factors : Factors) (signed : Finset (BitVec 160)) (address : ChainAddress)
    (step : Fin 7) (query : Query) (answer : BitVec 256) : Prop :=
  (query = chainInput address step (truncate (factors.1 (predecessor address step))) →
    Authorized factors.2.2 signed (predecessor address step)) ∧
  (query ≠ chainInput address step (truncate (factors.1 (predecessor address step))) →
    truncate answer ≠ truncate (factors.1 (successor address step)))

/-- The actual chain-query monitor preserves both cache invariants and rules out
both contact types whenever it returns normally. -/
theorem chain_read_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (address : ChainAddress) (step : Fin 7) (query : Query)
    (located : locate query = some (.chain address step)) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.chainStep exposed cache address step query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe factors signed result.2.1 result.2.2 ∧ ChainClean factors signed address step query result.1 := by
  rw [stopped_chain _ _ _ _ _ _ _ initial.1 (initial.2.2.chain factors cache query address step located)] at member
  unfold chainStopped at member
  by_cases canonical : query = chainInput address step (truncate (factors.1 (predecessor address step)))
  · rw [if_pos canonical] at member
    cases present : exposed (predecessor address step) with
    | none => simp only [present, if_true, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
    | some value =>
      simp only [present, Option.some_ne_none, if_false, stopped, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      have authorized := initial.2.1 _ value present
      refine ⟨⟨initial.1.cacheQuery _, ?_, initial.2.2⟩, ?_⟩
      · exact initial.2.1.cacheQuery _ _ _ _ _ (authorized_successor _ _ _ _ authorized)
      · exact ⟨fun _ => authorized, fun different => False.elim (different canonical)⟩
  · rw [if_neg canonical] at member
    have different : query ≠ (Position.chain address step).input (privateTable factors) (labels factors) := by
      rw [canonical_chain_input]
      exact canonical
    have safe := residual_read_safe factors signed exposed cache initial query (.chain address step)
      located different result member
    exact ⟨safe.1, fun matched => False.elim (canonical matched), fun _ => safe.2⟩

end SigGolfCandidate.Hypertree.SecurityGraphMonitorChainState
