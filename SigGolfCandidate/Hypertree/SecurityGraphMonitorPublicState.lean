import SigGolfCandidate.Hypertree.SecurityGraphMonitorChainState
import SigGolfCandidate.Hypertree.SecurityGraphMonitorMetadata

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor
  SecurityGraphAuthorization SecurityGraphPublicMonitor
  SecurityGraphMonitorProgram SecurityGraphMonitorInvariant SecurityGraphMonitorChainState
  SecurityGraphMonitorMetadata
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

theorem required_authorized (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (position : Position) : ∀ point ∈ required position, Authorized metadata signed point := by
  cases position with
  | chain address step => simp only [required, List.not_mem_nil, false_implies, implies_true]
  | leaf level tree side =>
    intro point member
    obtain ⟨chain, same⟩ := List.mem_ofFn.mp member
    rw [← same]
    exact endpoint_authorized metadata signed _
  | node level tree =>
    by_cases bottom : level.val = 0
    · intro point member
      simp only [required, if_pos bottom, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst point <;>
        exact bottom_positive_authorized metadata signed _ 1 bottom (by decide)
    · simp only [required, if_neg bottom, List.not_mem_nil, false_implies, implies_true]

theorem metadata_state_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (position : Position) :
    Safe factors signed (revealCache factors.1 (required position) exposed) cache :=
  ⟨initial.1.revealCache _, initial.2.1.revealCache factors.2.2 signed factors.1
    (required position) exposed (required_authorized factors.2.2 signed position), initial.2.2⟩

/-- Every normally completed metadata query preserves the actual exposure and
residual-cache invariants and cannot be a wrong-input target collision. -/
theorem nonchain_read_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (position : Position) (query : Query) (located : locate query = some position)
    (nonchain : ∀ address step, position ≠ Position.chain address step) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe factors signed result.2.1 result.2.2 ∧
      (query ≠ position.input (privateTable factors) (labels factors) →
        truncate result.1 ≠ truncate (labels factors position)) := by
  have clean : CacheMissTarget cache query (truncate (labels factors position)) :=
    fun answer present => (initial.2.2 query answer present position located).2
  rw [stopped_public_nonchain _ factors.2.1 _ _ _ _ _ _ located nonchain clean] at member
  unfold metadataStopped at member
  by_cases canonical : query = position.input (privateTable factors) (labels factors)
  · simp only [if_pos canonical, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact ⟨metadata_state_safe factors signed exposed cache initial position,
      fun different => False.elim (different canonical)⟩
  · rw [if_neg canonical] at member
    have safe := residual_read_safe factors signed _ cache
      (metadata_state_safe factors signed exposed cache initial position)
      query position located canonical result member
    exact ⟨safe.1, fun _ => safe.2⟩

/-- Inputs outside graph addresses cannot affect any graph target invariant. -/
theorem outside_read_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (located : locate query = none) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe factors signed result.2.1 result.2.2 := by
  rw [stopped_public_outside _ factors.2.1 _ _ _ _ _ located] at member
  simp only [SecurityGraphOracle.publicOracle, SecurityGraphOracle.canonical, located] at member
  cases present : cache query with
  | some answer =>
    simp only [randomOracle.run_eq, present, pure_bind, stopped, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact initial
  | none =>
    simp only [randomOracle.run_eq, present, bind_assoc, pure_bind, stopped, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    obtain ⟨answer, _, same⟩ := member
    subst result
    refine ⟨initial.1, initial.2.1, initial.2.2.cacheQuery factors cache query answer ?_⟩
    intro position impossible
    rw [located] at impossible
    cases impossible

/-- The state invariant holds after every public query, for every malformed input
and every cache state reachable before contact. -/
theorem public_read_safe (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe factors signed result.2.1 result.2.2 := by
  cases located : locate query with
  | none => exact outside_read_safe factors signed exposed cache initial query located result member
  | some position =>
    cases position with
    | chain address step =>
      have dispatch : SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
          (fun answer opened residual => Program.done (answer, opened, residual)) =
          SecurityGraphMonitorOracle.chainStep exposed cache address step query
            (fun answer opened residual => Program.done (answer, opened, residual)) := by
        simp only [SecurityGraphMonitorOracle.publicStep, located]
      rw [dispatch] at member
      exact (chain_read_safe factors signed exposed cache initial address step query located result member).1
    | leaf level tree side =>
      exact (nonchain_read_safe factors signed exposed cache initial _ query located
        (by intros; intro h; cases h) result member).1
    | node level tree =>
      exact (nonchain_read_safe factors signed exposed cache initial _ query located
        (by intros; intro h; cases h) result member).1

end SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicState
