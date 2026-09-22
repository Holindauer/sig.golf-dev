import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
import SigGolfCandidate.Hypertree.SecurityGraphMonitorStop
import SigGolfCandidate.Hypertree.SecurityGraphOracle

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorMetadata
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor
  SecurityGraphPublicMonitor SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- Repeated residual inputs cannot hide an earlier output collision. -/
def CacheMissTarget (cache : QueryCache HashSpec) (query : Query) (target : Digest) : Prop :=
  ∀ answer, cache query = some answer → truncate answer ≠ target

/-- Disclosing metadata dependencies is exact and never sets the stopped flag. -/
theorem stopped_disclose {α : Type} (table : PointTable) (points : List Point)
    (exposed : QueryCache PointSpec) (next : QueryCache PointSpec → Program α) :
    stopped table exposed (SecurityGraphMonitorOracle.disclose points exposed next) =
      stopped table (revealCache table points exposed) (next (revealCache table points exposed)) := by
  induction points generalizing exposed with
  | nil => rfl
  | cons point points ih => exact ih (exposed.cacheQuery point (table point))

/-- Exact stopped residual semantics for a publicly known metadata target. -/
theorem stopped_knownResidual_some {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (clean : CacheMissTarget cache query target) :
    stopped table exposed (SecurityGraphMonitorOracle.knownResidual exposed cache query (some target) next) =
      (do
        let result ← (randomOracle (spec := HashSpec) query).run cache
        if truncate result.1 = target then pure none
        else stopped table exposed (next result.1 exposed result.2)) := by
  cases present : cache query with
  | some answer =>
    have miss := clean answer present
    simp only [SecurityGraphMonitorOracle.knownResidual, present, randomOracle.run_eq, pure_bind, if_neg miss]
  | none =>
    simp only [SecurityGraphMonitorOracle.knownResidual, present, stopped, randomOracle.run_eq,
      bind_assoc, pure_bind]

/-- Queries with no graph address use the residual oracle without a graph-target test. -/
theorem stopped_knownResidual_none {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    stopped table exposed (SecurityGraphMonitorOracle.knownResidual exposed cache query none next) =
      (do
        let result ← (randomOracle (spec := HashSpec) query).run cache
        stopped table exposed (next result.1 exposed result.2)) := by
  cases present : cache query <;>
    simp only [SecurityGraphMonitorOracle.knownResidual, present, stopped, randomOracle.run_eq,
      bind_assoc, pure_bind]

theorem metadata_label (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (position : Position)
    (nonchain : ∀ address step, position ≠ Position.chain address step) :
    labels (viewFactors exposed metadata) position = labels (table, (nonces, metadata)) position := by
  cases position with
  | chain address step => exact False.elim (nonchain address step rfl)
  | leaf level tree side => rfl
  | node level tree => rfl

/-- Stopped leaf/node semantics written with the actual fixed canonical payload
and output, rather than the monitor's reconstructed view. -/
noncomputable def metadataStopped {α : Type} (table : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : ProbComp (Option α) :=
  let factors := (table, (nonces, metadata))
  let opened := revealCache table (required position) exposed
  if query = position.input (privateTable factors) (labels factors) then
    stopped table opened (next (labels factors position) opened cache)
  else do
    let result ← (randomOracle (spec := HashSpec) query).run cache
    if truncate result.1 = truncate (labels factors position) then pure none
    else stopped table opened (next result.1 opened result.2)

/-- One nonchain public query has exactly the canonical-or-residual stopped
semantics. Every dependency is disclosed, so no initial exposure assumption is needed. -/
theorem stopped_public_nonchain {α : Type} (table : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (located : locate query = some position)
    (nonchain : ∀ address step, position ≠ Position.chain address step)
    (clean : CacheMissTarget cache query (truncate (labels (table, (nonces, metadata)) position))) :
    stopped table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) =
      metadataStopped table nonces metadata exposed cache position query next := by
  have dispatch : SecurityGraphMonitorOracle.publicStep metadata exposed cache query next =
      SecurityGraphMonitorOracle.disclose (required position) exposed (fun opened =>
        let factors := viewFactors opened metadata
        if query = position.input (privateTable factors) (labels factors) then
          next (labels factors position) opened cache
        else SecurityGraphMonitorOracle.knownResidual opened cache query
          (some (truncate (labels factors position))) next) := by
    cases position with
    | chain address step => exact False.elim (nonchain address step rfl)
    | leaf level tree side | node level tree => simp only [SecurityGraphMonitorOracle.publicStep, located]
  rw [dispatch, stopped_disclose]
  let opened := revealCache table (required position) exposed
  have payloadEq := required_input table nonces metadata opened position nonchain
    (fun point member => revealCache_mem table (required position) exposed point member)
  have labelEq := metadata_label table nonces metadata opened position nonchain
  change stopped table opened (if query = _ then _ else _) = _
  rw [payloadEq, labelEq]
  unfold metadataStopped
  by_cases matched : query = position.input (privateTable (table, (nonces, metadata)))
      (labels (table, (nonces, metadata)))
  · simp only [if_pos matched]
    rfl
  · simp only [if_neg matched]
    exact stopped_knownResidual_some table opened cache query _ next clean

/-- The disclosed cache still agrees with the true fixed point table. -/
theorem metadata_opened_agree (table : PointTable) (exposed : QueryCache PointSpec)
    (position : Position) (agree : Agree table exposed) :
    Agree table (revealCache table (required position) exposed) := agree.revealCache (required position)

/-- Operational expression through the actual explicit graph oracle. Canonical
returns are not collision-tested; only noncanonical residual responses are tested. -/
theorem metadataStopped_publicOracle {α : Type} (table : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (located : locate query = some position) :
    metadataStopped table nonces metadata exposed cache position query next =
      (do
        let result ← (SecurityGraphOracle.publicOracle (privateTable (table, (nonces, metadata)))
          (labels (table, (nonces, metadata))) query).run cache
        if query ≠ position.input (privateTable (table, (nonces, metadata))) (labels (table, (nonces, metadata))) ∧
            truncate result.1 = truncate (labels (table, (nonces, metadata)) position) then pure none
        else
          let opened := revealCache table (required position) exposed
          stopped table opened (next result.1 opened result.2)) := by
  unfold metadataStopped SecurityGraphOracle.publicOracle SecurityGraphOracle.canonical
  rw [located]
  by_cases matched : query = position.input (privateTable (table, (nonces, metadata)))
      (labels (table, (nonces, metadata)))
  · simp [matched]
  · simp [matched]

/-- Direct leaf/node coupling through the same graph oracle used by the actual
reference experiment, retaining the arbitrary continuation and residual state. -/
theorem stopped_public_nonchain_oracle {α : Type} (table : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (located : locate query = some position)
    (nonchain : ∀ address step, position ≠ Position.chain address step)
    (clean : CacheMissTarget cache query (truncate (labels (table, (nonces, metadata)) position))) :
    stopped table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) =
      (do
        let result ← (SecurityGraphOracle.publicOracle (privateTable (table, (nonces, metadata)))
          (labels (table, (nonces, metadata))) query).run cache
        if query ≠ position.input (privateTable (table, (nonces, metadata))) (labels (table, (nonces, metadata))) ∧
            truncate result.1 = truncate (labels (table, (nonces, metadata)) position) then pure none
        else
          let opened := revealCache table (required position) exposed
          stopped table opened (next result.1 opened result.2)) := by
  rw [stopped_public_nonchain table nonces metadata exposed cache position query next located nonchain clean,
    metadataStopped_publicOracle table nonces metadata exposed cache position query next located]

/-- Inputs outside all graph addresses have no graph-contact test at all. -/
theorem stopped_public_outside {α : Type} (table : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (located : locate query = none) :
    stopped table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) =
      (do
        let result ← (SecurityGraphOracle.publicOracle (privateTable (table, (nonces, metadata)))
          (labels (table, (nonces, metadata))) query).run cache
        stopped table exposed (next result.1 exposed result.2)) := by
  simp only [SecurityGraphMonitorOracle.publicStep, located, SecurityGraphOracle.publicOracle,
    SecurityGraphOracle.canonical]
  exact stopped_knownResidual_none table exposed cache query next

end SigGolfCandidate.Hypertree.SecurityGraphMonitorMetadata
