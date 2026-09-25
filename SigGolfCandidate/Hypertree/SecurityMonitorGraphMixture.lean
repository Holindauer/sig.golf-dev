import SigGolfCandidate.Hypertree.SecurityMonitorGraphCoupling
import SigGolfCandidate.Hypertree.SecurityMonitorCombined

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphMixture
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

abbrev TrueResult := NonceTable × SecurityMonitorGraphView.Result SecurityExperiment.Result

/-- The actual graph oracle, with precisely the independently sampled factors
and joint output used by the common passive simulation. -/
noncomputable def joint (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp TrueResult := do
  let nonces ← $ᵗ NonceTable
  let metadata ← $ᵗ MetadataTable
  let points ← $ᵗ PointTable
  let pk := truncate (metadata (.node 159 0))
  let result ← SecurityMonitorGraphCoupling.start (points, (nonces, metadata)) pk
    (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}) budget
  pure (nonces, result)

/-- The graph game hop transports an arbitrary joint event; in particular its
secret key component is retained rather than added from another distribution. -/
theorem joint_le_union (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (event : TrueResult → Prop) :
    Pr[event | joint publicCache adversary rounds budget] ≤
      Pr[fun result => result.2.bad = true ∨ event (result.1, result.2.value) |
        SecurityMonitorNonceView.joint publicCache adversary rounds budget] := by
  simp only [joint, SecurityMonitorNonceView.joint, bind_pure_comp, probEvent_bind_eq_tsum,
    probEvent_map, Function.comp_def]
  apply ENNReal.tsum_le_tsum
  intro nonces
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro metadata
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro points
  apply mul_le_mul' le_rfl
  exact SecurityMonitorGraphCoupling.start_le_union (points, (nonces, metadata)) _ _ budget
    (fun result => event (nonces, result))

noncomputable def experiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp (SecuritySecretKeyMonitor.Outcome TrueResult) :=
  SecuritySecretKeyMonitor.experiment (joint publicCache adversary rounds budget) (fun result => result.2.history.secretKeyInputs)

/-- Exact same-secret key, same-history union transfer to the fully concrete common
experiment whose four-event probability has already been bounded. -/
theorem experiment_le_union (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (event : SecretKey → TrueResult → Prop) :
    Pr[fun result => event result.secretKey result.value | experiment publicCache adversary rounds budget] ≤
      Pr[fun result => SecurityMonitorCombined.GraphBad result ∨
        event result.secretKey (result.value.1, result.value.2.value) |
        SecurityMonitorCombined.experiment publicCache adversary rounds budget] := by
  have left := SecuritySecretKeyMonitor.secretKey_first (joint publicCache adversary rounds budget)
    (fun result => result.2.history.secretKeyInputs)
  have right := SecuritySecretKeyMonitor.secretKey_first (SecurityMonitorNonceView.joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs)
  have levent := probEvent_congr' (p := fun result => event result.secretKey result.value)
    (q := fun result => event result.secretKey result.value) (fun _ _ => Iff.rfl) left
  have revent := probEvent_congr' (p := fun result => SecurityMonitorCombined.GraphBad result ∨
      event result.secretKey (result.value.1, result.value.2.value))
    (q := fun result => SecurityMonitorCombined.GraphBad result ∨
      event result.secretKey (result.value.1, result.value.2.value)) (fun _ _ => Iff.rfl) right
  change Pr[fun result => event result.secretKey result.value | SecuritySecretKeyMonitor.experiment _ _] ≤ _
  rw [levent]
  change _ ≤ Pr[fun result => SecurityMonitorCombined.GraphBad result ∨
    event result.secretKey (result.value.1, result.value.2.value) | SecuritySecretKeyMonitor.experiment _ _]
  rw [revent]
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    SecuritySecretKeyMonitor.annotate, SecurityMonitorCombined.GraphBad]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  exact mul_le_mul' le_rfl (joint_le_union publicCache adversary rounds budget (event secretKey))

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphMixture.experiment_le_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_le_union
end SigGolfCandidate.Hypertree.SecurityMonitorGraphMixture
