import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor
  SecurityGraphAuthorization SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityGraphMonitorInvariant SecurityGraphMonitorChainState SecurityGraphMonitorPublicState
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorNoContact SecurityMonitorIndexState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

def Ready (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) : Prop :=
  Safe factors history.signedIndices exposed residual ∧ PublicReady factors.1 exposed

theorem PublicReady.cacheQuery {table : PointTable} {exposed : QueryCache PointSpec}
    (ready : PublicReady table exposed) (point : Point) :
    PublicReady table (exposed.cacheQuery point (table point)) := ready.reveal [point]

theorem opened_ready (factors : Factors) (exposed : QueryCache PointSpec) (query : Query)
    (ready : PublicReady factors.1 exposed) : PublicReady factors.1 (opened factors exposed query) := by
  unfold opened
  cases locate query with
  | none => exact ready
  | some position =>
    cases position with
    | chain address step =>
      dsimp only
      split
      · exact PublicReady.cacheQuery ready _
      · exact ready
    | leaf level tree side | node level tree => exact ready.reveal _

theorem parsed_indices (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (eligible cached : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed eligible cached answer).signedIndices = history.signedIndices := by
  cases parsed with
  | some pair => rfl
  | none => cases eligible <;> rfl

attribute [local irreducible] recordParsed

theorem public_indices (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    (recordPublic pk history query cached answer).signedIndices = history.signedIndices :=
  parsed_indices history query (SecurityIndexQuery.parse pk query)
    (decide (SecuritySeparation.SeedEligible query)) cached answer

/-- The concrete public step preserves everything required to execute future
honest signing macros, including the public endpoint disclosures. -/
theorem public_ready (factors : Factors) (pk : PublicKey) (history : History)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Ready factors history exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Ready factors (recordPublic pk history query (cache query).isSome result.1) result.2.1 result.2.2 := by
  have safe := public_read_safe factors history.signedIndices exposed cache initial.1 query result member
  have spec := read_spec factors history.signedIndices exposed cache initial.1 query result member
  refine ⟨?_, ?_⟩
  · simpa only [public_indices] using safe
  · rw [spec.2.2.1]
    exact opened_ready factors exposed query initial.2

/-- The selected honest signature coordinates are authorized after inserting
this signing index; point selection itself depends only on disclosed metadata. -/
theorem needed_authorized (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (ready : PublicReady factors.1 exposed) (index : BitVec 160) :
    ∀ point ∈ needed factors.2.2 exposed index,
      Authorized factors.2.2 (insert index history.signedIndices) point := by
  intro point member
  rw [needed, Finset.mem_toList] at member
  have same := signaturePoints_congr _ _ (metadata_ready factors.1 factors.2.1 factors.2.2 exposed ready) index
  rw [same] at member
  exact signaturePoints_authorized factors (insert index history.signedIndices) index (Finset.mem_insert_self ..)
    point member

/-- A completed H5 lookup plus honest disclosure preserves the full graph state.
The raw H5 answer, and therefore the exact signed index, are retained. -/
theorem sign_ready (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (initial : Ready factors history exposed cache)
    (pk : PublicKey) (message : Message) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer, residual) ∈ support ((randomOracle (spec := HashSpec)
      (SecurityRandomOracle.indexInput pk message (factors.2.1 message))).run cache)) :
    Ready factors (recordSign history message
      (cache (SecurityRandomOracle.indexInput pk message (factors.2.1 message))).isSome answer)
      (revealCache factors.1 (needed factors.2.2 exposed (answer.extractLsb' 0 160)) exposed) residual := by
  have safeResidual : ResidualSafe factors residual := by
    let query := SecurityRandomOracle.indexInput pk message (factors.2.1 message)
    have outside := SecurityIndexQuery.locate_index pk message (factors.2.1 message)
    change (answer, residual) ∈ support ((randomOracle (spec := HashSpec) query).run cache) at member
    cases present : cache query with
    | some value =>
      simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
      exact member.2 ▸ initial.1.2.2
    | none =>
      simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
      obtain ⟨value, _, equal⟩ := member
      cases equal
      apply initial.1.2.2.cacheQuery factors cache query answer
      intro position impossible
      rw [outside] at impossible
      cases impossible
  refine ⟨⟨initial.1.1.revealCache _, ?_, safeResidual⟩, initial.2.reveal _⟩
  apply ExposedSafe.revealCache
  · exact initial.1.2.1.mono factors.2.2 (fun _ member => Finset.mem_insert_of_mem member) exposed
  · exact needed_authorized factors history exposed initial.2 _

/-- The actual finite setup reveal prefix establishes the state invariant. -/
theorem setup_ready (factors : Factors) :
    Ready factors (recordKeygen {}) (SecurityGraphMonitorSetup.cache factors.1 factors.2.2) ∅ := by
  refine ⟨⟨SecurityGraphMonitorSetup.cache_agree _ _, ?_, residualSafe_empty factors⟩,
    SecurityGraphMonitorSetup.cache_publicReady _ _⟩
  exact SecurityGraphMonitorSetup.cache_authorized factors.1 factors.2.2

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphState.sign_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_ready
end SigGolfCandidate.Hypertree.SecurityMonitorGraphState
