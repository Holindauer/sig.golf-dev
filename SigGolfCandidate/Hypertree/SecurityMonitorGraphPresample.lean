import SigGolfCandidate.Hypertree.SecurityMonitorGraphMixture

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphPresample
open SigGolf OracleComp OracleSpec SecurityGameHop SecurityGraphIdeal SecurityGraphFactor
  SecurityGraphOracle SecurityMonitorViewAtomic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

/-- Original ideal-game execution through independent factors, in the exact
sampling order used by the common passive experiment. The output may retain
both a cutoff result and its secret key-query trace. -/
theorem ideal_factors {α : Type} (program : OracleComp GameWorld α) :
    𝒮[(simulateQ idealGameOracle program).run' (∅, ∅)] =
      𝒮[do
        let nonces ← $ᵗ NonceTable
        let metadata ← $ᵗ MetadataTable
        let points ← $ᵗ SecurityGraphPassive.PointTable
        let factors := (points, (nonces, metadata))
        (simulateQ (gameImplementation (privateTable factors) (labels factors)) program).run' ∅] := by
  change 𝒮[idealObserve program ∅ ∅] = _
  rw [ideal_graph, graphObserve_factors]
  calc
    _ = 𝒮[do
        let points ← $ᵗ SecurityGraphPassive.PointTable
        let nonces ← $ᵗ NonceTable
        let metadata ← $ᵗ MetadataTable
        let factors := (points, (nonces, metadata))
        (simulateQ (gameImplementation (privateTable factors) (labels factors)) program).run' ∅] := by
      apply evalSPMF_bind_congr
      intro points _
      apply evalSPMF_bind_congr
      intro nonces _
      apply evalSPMF_bind_congr
      intro metadata _
      dsimp only
      rw [routing]
      exact congrArg evalSPMF (observe_eq _ _ _ ∅)
    _ = 𝒮[do
        let nonces ← $ᵗ NonceTable
        let points ← $ᵗ SecurityGraphPassive.PointTable
        let metadata ← $ᵗ MetadataTable
        let factors := (points, (nonces, metadata))
        (simulateQ (gameImplementation (privateTable factors) (labels factors)) program).run' ∅] :=
      evalSPMF_bind_bind_swap _ _ _
    _ = _ := by
      apply evalSPMF_bind_congr
      intro nonces _
      exact evalSPMF_bind_bind_swap _ _ _

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphPresample.ideal_factors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ideal_factors
end SigGolfCandidate.Hypertree.SecurityMonitorGraphPresample
