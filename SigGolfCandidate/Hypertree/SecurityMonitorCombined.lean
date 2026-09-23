import SigGolfCandidate.Hypertree.SecurityMonitorGraphCost
import SigGolfCandidate.Hypertree.SecurityMonitorGraphLifetime
import SigGolfCandidate.Hypertree.SecurityMonitorIndexBound
import SigGolfCandidate.Hypertree.SecurityMonitorNonceBound
import SigGolfCandidate.Hypertree.SecuritySecretKeyMonitor

namespace SigGolfCandidate.Hypertree.SecurityMonitorCombined
open SigGolf OracleComp OracleSpec OracleComp.EvalDist Reference SecurityGraphFactor
  SecurityMonitorIndexState SecuritySharedBudget SecurityMonitorNonceView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

abbrev Result := SecuritySecretKeyMonitor.Outcome JointResult

/-- All four bad events and all three charged query classes share one execution.
The uniform secret key is independent of the public simulation and is used only here. -/
noncomputable def experiment (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) : ProbComp Result :=
  SecuritySecretKeyMonitor.experiment (joint publicCache adversary rounds budget) (fun result => result.2.value.history.secretKeyInputs)

def history (result : Result) : History := result.value.2.value.history

def SecretKeyBad (result : Result) : Prop := result.bad = true
def GraphBad (result : Result) : Prop := result.value.2.bad = true
def NonceBad (result : Result) : Prop := hits result.value.1 (history result) = true
def IndexBad (result : Result) : Prop := SecurityIndexTrace.Conflict (history result).indexTrace

def Bad (result : Result) : Prop := SecretKeyBad result ∨ GraphBad result ∨ NonceBad result ∨ IndexBad result

attribute [local irreducible] SecurityMonitorGraphView.experiment joint

theorem joint_supported (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat)
    (result : JointResult) (member : result ∈ support (joint publicCache adversary rounds budget)) :
    result.2 ∈ support (SecurityMonitorGraphView.experiment publicCache adversary rounds budget) := by
  rw [← joint_marginal, support_map]
  exact ⟨result, member, rfl⟩

theorem supported (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat)
    (result : Result) (member : result ∈ support (experiment publicCache adversary rounds budget)) :
    result.value ∈ support (joint publicCache adversary rounds budget) := by
  simp only [experiment, SecuritySecretKeyMonitor.experiment, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at member
  obtain ⟨value, member, secretKey, _, same⟩ := member
  cases same
  exact member



theorem count_le (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat)
    (result : Result) (member : result ∈ support (experiment publicCache adversary rounds budget)) :
    (history result).counts.total ≤ budget :=
  SecurityMonitorGraphBudget.experiment_count_le publicCache adversary rounds budget _
    (joint_supported publicCache adversary rounds budget _ (supported publicCache adversary rounds budget result member))

theorem secretKey_bound (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[SecretKeyBad | experiment publicCache adversary rounds budget] ≤
      expectedValue (experiment publicCache adversary rounds budget) (fun result => ((history result).counts.secretKey : ENNReal)/2^128) := by
  have bound := SecuritySecretKeyMonitor.prob_bad_le_expected (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs)
  change Pr[SecretKeyBad | experiment publicCache adversary rounds budget] ≤
    expectedValue (experiment publicCache adversary rounds budget) (fun result => (result.calls : ENNReal))/2^128 at bound
  apply bound.trans
  rw [div_eq_mul_inv, ← expectedValue_mul_const]
  apply expectedValue_mono_of_support
  intro result member
  have counted := (SecurityMonitorGraphLifetime.experiment_history publicCache adversary rounds budget _
    (joint_supported publicCache adversary rounds budget _ (supported publicCache adversary rounds budget result member))).1
  have calls : result.calls ≤ (history result).secretKeyInputs.length := by
    have original := member
    simp only [experiment, SecuritySecretKeyMonitor.experiment, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at original
    obtain ⟨value, _, secretKey, _, same⟩ := original
    cases same
    exact List.length_filter_le _ _
  have small : result.calls ≤ (history result).counts.secretKey := calls.trans_eq counted.2.2.2
  exact mul_le_mul' (by exact_mod_cast small) le_rfl

theorem graph_bound (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[GraphBad | experiment publicCache adversary rounds budget] ≤
      expectedValue (experiment publicCache adversary rounds budget) (fun result => 2*((history result).counts.graph : ENNReal)/2^128) := by
  unfold GraphBad
  simp only [experiment, history]
  rw [SecuritySecretKeyMonitor.value_event (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => result.2.bad = true),
    SecuritySecretKeyMonitor.expected_value (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => 2*(result.2.value.history.counts.graph : ENNReal)/2^128)]
  have bound := SecurityMonitorGraphCost.experiment_bad_le publicCache adversary rounds budget
  rw [← joint_marginal, probEvent_map, expectedValue_map] at bound
  simpa only [Function.comp_def, div_eq_mul_inv, mul_comm (2 : ENNReal), expectedValue_mul_const] using bound

theorem nonce_bound (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[NonceBad | experiment publicCache adversary rounds budget] ≤
      expectedValue (experiment publicCache adversary rounds budget) (fun result => ((history result).counts.index : ENNReal)/2^256) := by
  unfold NonceBad
  simp only [experiment, history]
  rw [SecuritySecretKeyMonitor.value_event (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => hits result.1 result.2.value.history = true),
    SecuritySecretKeyMonitor.expected_value (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => (result.2.value.history.counts.index : ENNReal)/2^256)]
  apply (joint_nonce_bound publicCache adversary rounds budget).trans
  rw [div_eq_mul_inv, ← expectedValue_mul_const]
  apply expectedValue_mono_of_support
  intro result member
  have counted := (SecurityMonitorGraphLifetime.experiment_history publicCache adversary rounds budget result.2
    (joint_supported publicCache adversary rounds budget result member)).1
  exact mul_le_mul' (by exact_mod_cast counted.2.2.1) le_rfl

theorem index_bound (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[IndexBad | experiment publicCache adversary rounds budget] ≤
      expectedValue (experiment publicCache adversary rounds budget) (fun result => ((history result).counts.index : ENNReal)/2^128) := by
  unfold IndexBad
  simp only [experiment, history]
  rw [SecuritySecretKeyMonitor.value_event (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => SecurityIndexTrace.Conflict result.2.value.history.indexTrace),
    SecuritySecretKeyMonitor.expected_value (joint publicCache adversary rounds budget)
    (fun result => result.2.value.history.secretKeyInputs) (fun result => (result.2.value.history.counts.index : ENNReal)/2^128)]
  have bound := SecurityMonitorIndexBound.experiment_bad_le publicCache adversary rounds budget
  have event : Pr[fun result => SecurityIndexTrace.Conflict result.value.history.indexTrace |
      SecurityMonitorGraphView.experiment publicCache adversary rounds budget] =
      Pr[fun result => SecurityMonitorIndexBound.Bad result.value.history |
        SecurityMonitorGraphView.experiment publicCache adversary rounds budget] := by
    apply probEvent_congr' _ rfl
    intro result member
    exact (and_iff_left (SecurityMonitorGraphLifetime.experiment_marks publicCache adversary rounds budget result member)).symm
  rw [← event, ← joint_marginal, probEvent_map, expectedValue_map] at bound
  apply bound.trans
  rw [div_eq_mul_inv, ← expectedValue_mul_const]
  apply expectedValue_mono_of_support
  intro result member
  have counted := (SecurityMonitorGraphLifetime.experiment_history publicCache adversary rounds budget result.2
    (joint_supported publicCache adversary rounds budget result member)).1
  exact mul_le_mul' (by exact_mod_cast counted.2.1) le_rfl

/-- Concrete combined bound, with no uninstantiated probability or resource
hypotheses: one total cutoff pays for all bad events in the same simulation. -/
theorem bad_le (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[Bad | experiment publicCache adversary rounds budget] ≤ (budget : ENNReal)/2^127 :=
  SecuritySharedBudget.prob_union_le (experiment publicCache adversary rounds budget)
    (fun result => (history result).counts) budget SecretKeyBad GraphBad NonceBad IndexBad
    (count_le publicCache adversary rounds budget) (secretKey_bound publicCache adversary rounds budget)
    (graph_bound publicCache adversary rounds budget) (nonce_bound publicCache adversary rounds budget)
    (index_bound publicCache adversary rounds budget)

#print axioms bad_le
end SigGolfCandidate.Hypertree.SecurityMonitorCombined
