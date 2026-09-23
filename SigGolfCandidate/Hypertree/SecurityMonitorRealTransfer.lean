import SigGolfCandidate.Hypertree.SecurityMonitorGraphPresample
import SigGolfCandidate.Hypertree.SecurityActualCutoff
import SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
import SigGolfCandidate.Hypertree.SecuritySecretKeyTraceProgram
import SigGolfCandidate.Hypertree.SecurityMonitorSecretKeyInputs
import SigGolfCandidate.Hypertree.SecurityMonitorWinBound

namespace SigGolfCandidate.Hypertree.SecurityMonitorRealTransfer
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecuritySecretKey SecurityGameHop
  SecurityGraphFactor SecurityMonitorViewAtomic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false
open scoped Classical

abbrev TraceResult := Option SecurityExperiment.Result × List Query

/-- The complete cutoff output and chronological secret key-eligible public trace,
interpreted in independent graph factors. Budget aborts remain ordinary outputs. -/
noncomputable def factorTrace (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp TraceResult := do
  let nonces ← $ᵗ NonceTable
  let metadata ← $ᵗ MetadataTable
  let points ← $ᵗ SecurityGraphPassive.PointTable
  let factors := (points, (nonces, metadata))
  (simulateQ (gameImplementation (privateTable factors) (labels factors))
    (tracePublic (SecurityBudget.cutoff (SecurityExperiment.program publicCache adversary rounds) budget))).run' ∅

theorem ideal_trace_eq (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    𝒮[(simulateQ idealGameOracle
      (tracePublic (SecurityBudget.cutoff (SecurityExperiment.program publicCache adversary rounds) budget))).run' (∅, ∅)] =
      𝒮[factorTrace publicCache adversary rounds budget] :=
  SecurityMonitorGraphPresample.ideal_factors _

/-- First real-game transfer. The secret key failure is inside the same traced graph
experiment as the surviving win, not charged as a cost from another game. -/
theorem real_le_factor_union (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[SecurityActualCutoff.Won | SecurityActualCutoff.experiment publicCache adversary rounds budget] ≤
      Pr[fun result => SecurityActualCutoff.Won result.2.1 ∨ SecretKeyHitTrace result.2.2 result.1 |
        (do let secretKey ← sampleSecretKey
            let trace ← factorTrace publicCache adversary rounds budget
            pure (secretKey, trace))] := by
  simp only [SecurityActualCutoff.experiment, bind_pure_comp, probEvent_bind_eq_tsum,
    probEvent_map, Function.comp_def]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  have equality := probEvent_congr'
    (p := fun result : TraceResult => SecurityActualCutoff.Won result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (q := fun result : TraceResult => SecurityActualCutoff.Won result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (fun _ _ => Iff.rfl) (ideal_trace_eq publicCache adversary rounds budget)
  rw [← equality]
  exact SecuritySecretKeyStoppedTrace.real_cutoff_le_ideal_union secretKey
    (SecurityExperiment.program publicCache adversary rounds) budget SecurityActualCutoff.Won

def projectJoint (result : SecurityMonitorGraphMixture.TrueResult) : TraceResult :=
  (result.2.value, result.2.history.secretKeyInputs.reverse)

/-- Atomic honest execution preserves the actual cutoff output and every
eligible public query in the true graph mixture. -/
theorem factorTrace_project (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    𝒮[factorTrace publicCache adversary rounds budget] =
      𝒮[projectJoint <$> SecurityMonitorGraphMixture.joint publicCache adversary rounds budget] := by
  simp only [factorTrace, SecurityMonitorGraphMixture.joint, map_bind, bind_pure_comp, Functor.map_map]
  apply evalSPMF_bind_congr
  intro nonces _
  apply evalSPMF_bind_congr
  intro metadata _
  apply evalSPMF_bind_congr
  intro points _
  have projection : (fun a => projectJoint (nonces, a)) = SecuritySecretKeyTraceView.project := by
    funext result
    rfl
  rw [projection]
  exact SecuritySecretKeyTraceView.traced_program (points, (nonces, metadata)) publicCache adversary rounds budget

theorem joint_eligible (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : SecurityMonitorGraphMixture.TrueResult)
    (member : result ∈ support (SecurityMonitorGraphMixture.joint publicCache adversary rounds budget)) :
    SecurityMonitorSecretKeyInputs.Eligible result.2.history := by
  simp only [SecurityMonitorGraphMixture.joint, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at member
  obtain ⟨nonces, _, metadata, _, points, _, outcome, member, equal⟩ := member
  cases equal
  exact SecurityMonitorSecretKeyInputs.start_eligible _ _ _ _ outcome member

attribute [local irreducible] SecurityMonitorGraphMixture.joint SecurityMonitorCombined.experiment
  SecurityMonitorNonceView.joint

/-- The secret key contact and the surviving win occur in one actual true-graph
mixture, including all ordinary budget failures and their retained histories. -/
theorem real_le_true_union (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[SecurityActualCutoff.Won | SecurityActualCutoff.experiment publicCache adversary rounds budget] ≤
      Pr[fun result => SecurityActualCutoff.Won result.value.2.value ∨
        SecuritySecretKeyMonitor.Hit result.value.2.history.secretKeyInputs result.secretKey |
        SecurityMonitorGraphMixture.experiment publicCache adversary rounds budget] := by
  have bound := real_le_factor_union publicCache adversary rounds budget
  apply bound.trans
  have first := SecuritySecretKeyMonitor.secretKey_first (SecurityMonitorGraphMixture.joint publicCache adversary rounds budget)
    (fun result => result.2.history.secretKeyInputs)
  have eventEq := probEvent_congr'
    (p := fun result => SecurityActualCutoff.Won result.value.2.value ∨
      SecuritySecretKeyMonitor.Hit result.value.2.history.secretKeyInputs result.secretKey)
    (q := fun result => SecurityActualCutoff.Won result.value.2.value ∨
      SecuritySecretKeyMonitor.Hit result.value.2.history.secretKeyInputs result.secretKey)
    (fun _ _ => Iff.rfl) first
  change _ ≤ Pr[_ | SecuritySecretKeyMonitor.experiment _ _]
  rw [eventEq]
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    SecuritySecretKeyMonitor.annotate]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  have same := probEvent_congr'
    (p := fun result : TraceResult => SecurityActualCutoff.Won result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (q := fun result : TraceResult => SecurityActualCutoff.Won result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (fun _ _ => Iff.rfl) (factorTrace_project publicCache adversary rounds budget)
  rw [same, probEvent_map]
  apply probEvent_mono
  intro result member contact
  rcases contact with won | hit
  · exact Or.inl won
  · exact Or.inr ((SecurityMonitorSecretKeyInputs.hit_reverse_iff _
      (joint_eligible publicCache adversary rounds budget result member) secretKey).mp hit)

/-- Concrete real-cutoff to common-world event inclusion. All secret key, graph, nonce,
and index events will be charged in this one shared experiment. -/
theorem real_le_common_union (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[SecurityActualCutoff.Won | SecurityActualCutoff.experiment publicCache adversary rounds budget] ≤
      Pr[fun result => SecurityMonitorCombined.GraphBad result ∨ SecurityMonitorCombined.SecretKeyBad result ∨
        SecurityActualCutoff.Won result.value.2.value.value |
        SecurityMonitorCombined.experiment publicCache adversary rounds budget] := by
  apply (real_le_true_union publicCache adversary rounds budget).trans
  have bound := SecurityMonitorGraphMixture.experiment_le_union publicCache adversary rounds budget
    (fun secretKey result => SecurityActualCutoff.Won result.2.value ∨
      SecuritySecretKeyMonitor.Hit result.2.history.secretKeyInputs secretKey)
  apply bound.trans
  apply probEvent_mono
  intro result member contact
  rcases contact with graph | won | secretKey
  · exact Or.inl graph
  · exact Or.inr (Or.inr won)
  · right; left
    have annotation := member
    simp only [SecurityMonitorCombined.experiment, SecuritySecretKeyMonitor.experiment,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at annotation
    obtain ⟨value, _, chosen, _, equal⟩ := annotation
    cases equal
    exact decide_eq_true secretKey

/-- The actual winning event is covered by the four already bounded bad events
of the same concrete secretKeyed passive experiment. -/
theorem real_le_bad (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[SecurityActualCutoff.Won | SecurityActualCutoff.experiment publicCache adversary rounds budget] ≤
      Pr[SecurityMonitorCombined.Bad | SecurityMonitorCombined.experiment publicCache adversary rounds budget] := by
  apply (real_le_common_union publicCache adversary rounds budget).trans
  apply probEvent_mono
  intro result member contact
  rcases contact with graph | secretKey | won
  · exact Or.inr (Or.inl graph)
  · exact Or.inl secretKey
  · exact SecurityMonitorWin.supported_won_bad publicCache adversary rounds budget result member won

/-- Full quantitative security of the actual reference cutoff game. -/
theorem real_bound (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[SecurityActualCutoff.Won | SecurityActualCutoff.experiment publicCache adversary rounds budget] ≤
      (budget : ENNReal) / 2^127 :=
  (real_le_bad publicCache adversary rounds budget).trans
    (SecurityMonitorCombined.bad_le publicCache adversary rounds budget)

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorRealTransfer.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_bound
end SigGolfCandidate.Hypertree.SecurityMonitorRealTransfer
