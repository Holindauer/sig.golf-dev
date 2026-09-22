import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
import SigGolfCandidate.Hypertree.SecurityGraphMonitorStop

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphContact
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- Residual cache entries are safe before the first target contact. This is
needed for repeated inputs: a cache hit does not incur a second fresh-output test. -/
def CacheMiss (table : PointTable) (cache : QueryCache HashSpec) (query : Query) (target : Point) : Prop :=
  ∀ answer, cache query = some answer → truncate answer ≠ truncate (table target)

/-- Exact stopped residual lookup. Fresh answers are tested against the actual
fixed coordinate, regardless of whether it has already been disclosed. -/
theorem stopped_residual {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree table exposed) (clean : CacheMiss table cache query target) :
    stopped table exposed (SecurityGraphMonitorOracle.residualStep exposed cache query target next) =
      (do
        let result ← (randomOracle (spec := HashSpec) query).run cache
        if truncate result.1 = truncate (table target) then pure none
        else stopped table exposed (next result.1 exposed result.2)) := by
  cases present : cache query with
  | some answer =>
    have miss := clean answer present
    simp only [SecurityGraphMonitorOracle.residualStep, present, randomOracle.run_eq,
      pure_bind, if_neg miss]
  | none =>
    simp only [SecurityGraphMonitorOracle.residualStep, present, randomOracle.run_eq, bind_assoc, pure_bind]
    cases known : exposed target with
    | none => simp only [known, stopped, true_and, eq_comm]
    | some value =>
      have same := agree target value known
      simp only [known, stopped, same]

/-- The exact canonical chain input expressed in the independent point factors. -/
theorem canonical_chain_input (factors : Factors) (address : ChainAddress) (step : Fin 7) :
    (Position.chain address step).input (privateTable factors) (labels factors) =
      chainInput address step (truncate (factors.1 (predecessor address step))) := by
  unfold predecessor
  rw [← assembled_chainPoint factors address ⟨step.val, by omega⟩]
  rfl

/-- Stopped chain semantics in terms of the actual canonical-input predicate.
Unlike the executable passive monitor, this expression may inspect the secret
coordinate, because it is used only in the identical-until-bad coupling. -/
noncomputable def chainStopped {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : ProbComp (Option α) :=
  if query = chainInput address step (truncate (table (predecessor address step))) then
    if exposed (predecessor address step) = none then pure none else
      let answer := table (successor address step)
      let opened := exposed.cacheQuery (successor address step) answer
      stopped table opened (next answer opened cache)
  else do
    let result ← (randomOracle (spec := HashSpec) query).run cache
    if truncate result.1 = truncate (table (successor address step)) then pure none
    else stopped table exposed (next result.1 exposed result.2)

theorem stopped_chain {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree table exposed) (clean : CacheMiss table cache query (successor address step)) :
    stopped table exposed (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) =
      chainStopped table exposed cache address step query next := by
  have residual := stopped_residual table exposed cache query (successor address step) next agree clean
  unfold SecurityGraphMonitorOracle.chainStep chainStopped
  cases parsed : payload address step query with
  | none =>
    have different := payload_none parsed (truncate (table (predecessor address step)))
    simpa only [if_neg different] using residual
  | some point =>
    have canonical := known_matches_canonical table address step query point parsed
    cases known : exposed (predecessor address step) with
    | none =>
      dsimp only
      by_cases hit : point = truncate (table (predecessor address step))
      · have matched := canonical.mpr hit
        have reverse := hit.symm
        simp only [if_pos matched, known, stopped, true_and, reverse, if_true, payload_some parsed]
      · have different := fun same => hit (canonical.mp same)
        have missed : truncate (table (predecessor address step)) ≠ point := Ne.symm hit
        simpa only [if_neg different, stopped, known, true_and, if_neg missed] using residual
    | some value =>
      have same := agree _ value known
      dsimp only
      by_cases hit : point = truncate value
      · have matched := canonical.mpr (hit.trans (congrArg truncate same))
        simp only [if_pos hit, if_pos matched, known, Option.some_ne_none, if_false, stopped]
      · have different : query ≠ chainInput address step (truncate (table (predecessor address step))) := by
          intro matched
          exact hit ((canonical.mp matched).trans (congrArg truncate same.symm))
        simpa only [if_neg hit, if_neg different] using residual

end SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling
