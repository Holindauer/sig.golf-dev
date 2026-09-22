import SigGolfCandidate.Hypertree.SecurityGraphDisclosure
import SigGolfCandidate.Hypertree.SecurityGraphFactor
import SigGolfCandidate.Hypertree.SecurityGraphOracle

namespace SigGolfCandidate.Hypertree.SecurityGraphPublicMonitor
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Coordinates needed to reconstruct public leaf/node payloads. Upper leaves
use endpoints; bottom nodes use public preimage targets; upper nodes use metadata. -/
def required : Position → List Point
  | .chain _ _ => []
  | .leaf level tree side => List.ofFn (fun chain : Chain => (⟨level, tree, side, chain⟩, 7))
  | .node level tree => if level.val = 0 then
      [(⟨level, tree, false, 0⟩, 1), (⟨level, tree, true, 0⟩, 1)] else []

def viewFactors (cache : QueryCache PointSpec) (metadata : MetadataTable) : Factors :=
  (fun point => (cache point).getD 0, (fun _ => 0, metadata))

/-- A public-input payload reconstructed from its disclosed coordinates equals
the actual canonical payload; the placeholder values are never used at hidden points. -/
theorem required_input (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (cache : QueryCache PointSpec) (position : Position)
    (nonchain : ∀ address step, position ≠ Position.chain address step)
    (ready : ∀ point ∈ required position, cache point = some (table point)) :
    position.input (privateTable (viewFactors cache metadata)) (labels (viewFactors cache metadata)) =
      position.input (privateTable (table, (nonces, metadata))) (labels (table, (nonces, metadata))) := by
  cases position with
  | chain address step => exact False.elim (nonchain address step rfl)
  | leaf level tree side =>
    simp only [Position.input, Position.payload]
    apply congrArg ((Position.leaf level tree side).address.input)
    apply congrArg (List.flatMap bytes)
    apply congrArg List.ofFn
    funext chain
    have known := ready (⟨level, tree, side, chain⟩, 7)
      (List.mem_ofFn.mpr ⟨chain, rfl⟩)
    simp only [labels, viewFactors, show (6 : Fin 7).succ = (7 : Fin 8) from rfl, known, Option.getD_some]
  | node level tree =>
    by_cases bottom : level.val = 0
    · have left := ready (⟨level, tree, false, 0⟩, 1) (by simp [required, bottom])
      have right := ready (⟨level, tree, true, 0⟩, 1) (by simp [required, bottom])
      simp only [Position.input, Position.payload, if_pos bottom, labels, viewFactors, show (0 : Fin 7).succ = (1 : Fin 8) from rfl, left, right,
        Option.getD_some]
    · simp only [Position.input, Position.payload, if_neg bottom, labels, viewFactors]

/-- Residual lookup at an optional known public target. Inputs outside all graph
addresses cannot create graph collisions and add no monitor test. -/
noncomputable def knownResidual (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) : Strategy :=
  match cache query with
  | some answer => next answer exposed cache
  | none => match target with
    | none => .bits (fun answer => next answer exposed (cache.cacheQuery query answer))
    | some target => .collision target (fun answer => next answer exposed (cache.cacheQuery query answer))

/-- Explicit passive simulation of every public H query. Chain handling uses the
hidden-predecessor test; leaf/node handling reveals only safe public coordinates. -/
noncomputable def publicStep (metadata : MetadataTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) : Strategy :=
  match locate query with
  | none => knownResidual exposed cache query none next
  | some (.chain address step) => chainStep exposed cache address step query next
  | some position => disclose (required position) exposed (fun opened =>
      let factors := viewFactors opened metadata
      if query = position.input (privateTable factors) (labels factors) then
        next (labels factors position) opened cache
      else knownResidual opened cache query (some (truncate (labels factors position))) next)

theorem knownResidual_within (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) (budget : Nat)
    (bound : ∀ answer exposed cache, Within budget (next answer exposed cache)) :
    Within (budget + 1) (knownResidual exposed cache query target next) := by
  unfold knownResidual
  split
  next answer present => exact Within.weaken (bound answer exposed cache) (by omega)
  next fresh =>
    cases target with
    | none => exact Within.bits (fun answer => Within.weaken (bound answer _ _) (by omega))
    | some target => exact Within.collision (fun answer => bound answer _ _)

/-- Every public hash call uses at most two tests in the single passive monitor. -/
theorem publicStep_within (metadata : MetadataTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) (budget : Nat)
    (bound : ∀ answer exposed cache, Within budget (next answer exposed cache)) :
    Within (budget + 2) (publicStep metadata exposed cache query next) := by
  unfold publicStep
  cases located : locate query with
  | none => exact Within.weaken (knownResidual_within exposed cache query none next budget bound) (by omega)
  | some position =>
    cases position with
    | chain address step => exact chainStep_within exposed cache address step query next budget bound
    | leaf level tree side | node level tree =>
      apply disclose_within
      intro opened
      dsimp only
      split
      next canonical => exact Within.weaken (bound _ _ _) (by omega)
      next other => exact Within.weaken (knownResidual_within opened cache query _ next budget bound) (by omega)

end SigGolfCandidate.Hypertree.SecurityGraphPublicMonitor
