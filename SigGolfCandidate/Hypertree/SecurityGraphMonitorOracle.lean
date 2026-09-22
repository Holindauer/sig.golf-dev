import SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphPublicMonitor SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def disclose {α : Type} : List Point → QueryCache PointSpec →
    (QueryCache PointSpec → Program α) → Program α
  | [], cache, next => next cache
  | point :: points, cache, next => .reveal point (fun answer =>
      disclose points (cache.cacheQuery point answer) next)

noncomputable def residualStep {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : Program α :=
  match cache query with
  | some answer => next answer exposed cache
  | none => match exposed target with
    | some known => .collision (truncate known)
        (fun answer => next answer exposed (cache.cacheQuery query answer))
    | none => .bits (fun answer => .guess target (truncate answer)
        (next answer exposed (cache.cacheQuery query answer)))

noncomputable def chainStep {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : Program α :=
  match payload address step query with
  | none => residualStep exposed cache query (successor address step) next
  | some point => match exposed (predecessor address step) with
    | none => .guess (predecessor address step) point
        (residualStep exposed cache query (successor address step) next)
    | some known => if point = truncate known then
        .reveal (successor address step) (fun answer =>
          next answer (exposed.cacheQuery (successor address step) answer) cache)
      else residualStep exposed cache query (successor address step) next

noncomputable def knownResidual {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : Program α :=
  match cache query with
  | some answer => next answer exposed cache
  | none => match target with
    | none => .bits (fun answer => next answer exposed (cache.cacheQuery query answer))
    | some target => .collision target (fun answer => next answer exposed (cache.cacheQuery query answer))

/-- Output-preserving operational simulation of one actual public H call. -/
noncomputable def publicStep {α : Type} (metadata : MetadataTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : Program α :=
  match locate query with
  | none => knownResidual exposed cache query none next
  | some (.chain address step) => chainStep exposed cache address step query next
  | some position => disclose (required position) exposed (fun opened =>
      let factors := viewFactors opened metadata
      if query = position.input (privateTable factors) (labels factors) then
        next (labels factors position) opened cache
      else knownResidual opened cache query (some (truncate (labels factors position))) next)

@[simp] theorem erase_disclose {α : Type} (points : List Point) (cache : QueryCache PointSpec)
    (next : QueryCache PointSpec → Program α) :
    erase (disclose points cache next) =
      SecurityGraphDisclosure.disclose points cache (fun opened => erase (next opened)) := by
  induction points generalizing cache with
  | nil => rfl
  | cons point points ih =>
    simp only [disclose, SecurityGraphDisclosure.disclose, erase]
    exact congrArg (Strategy.reveal point) (funext (fun answer => ih _))

@[simp] theorem erase_residualStep {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    erase (residualStep exposed cache query target next) =
      SecurityGraphChainMonitor.residualStep exposed cache query target
        (fun answer opened residual => erase (next answer opened residual)) := by
  cases present : cache query with
  | some answer => simp only [residualStep, SecurityGraphChainMonitor.residualStep, present]
  | none => cases known : exposed target <;> simp only [residualStep, SecurityGraphChainMonitor.residualStep, present, known, erase]

@[simp] theorem erase_chainStep {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    erase (chainStep exposed cache address step query next) =
      SecurityGraphChainMonitor.chainStep exposed cache address step query
        (fun answer opened residual => erase (next answer opened residual)) := by
  unfold chainStep SecurityGraphChainMonitor.chainStep
  cases parsed : payload address step query with
  | none => exact erase_residualStep ..
  | some point =>
    cases known : exposed (predecessor address step) with
    | none => exact congrArg (Strategy.guess (predecessor address step) point) (erase_residualStep ..)
    | some answer =>
      dsimp only
      by_cases same : point = truncate answer
      · rw [if_pos same, if_pos same]
        rfl
      · rw [if_neg same, if_neg same]
        exact erase_residualStep ..

@[simp] theorem erase_knownResidual {α : Type} (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    erase (knownResidual exposed cache query target next) =
      SecurityGraphPublicMonitor.knownResidual exposed cache query target
        (fun answer opened residual => erase (next answer opened residual)) := by
  cases present : cache query with
  | some answer => simp only [knownResidual, SecurityGraphPublicMonitor.knownResidual, present]
  | none => cases target <;> simp only [knownResidual, SecurityGraphPublicMonitor.knownResidual, present, erase]

/-- Erasure recovers the exact existing two-tests-per-query monitor. -/
@[simp] theorem erase_publicStep {α : Type} (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    erase (publicStep metadata exposed cache query next) =
      SecurityGraphPublicMonitor.publicStep metadata exposed cache query
        (fun answer opened residual => erase (next answer opened residual)) := by
  unfold publicStep SecurityGraphPublicMonitor.publicStep
  cases located : locate query with
  | none => exact erase_knownResidual ..
  | some position =>
    cases position with
    | chain address step => exact erase_chainStep ..
    | leaf level tree side | node level tree =>
      rw [erase_disclose]
      congr 1
      funext opened
      dsimp only
      split <;> simp only [erase_knownResidual]

end SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
