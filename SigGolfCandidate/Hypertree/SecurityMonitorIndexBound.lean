import SigGolfCandidate.Hypertree.SecurityMonitorIndexTrace

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexBound
open SigGolf OracleComp OracleSpec OracleComp.EvalDist Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState SecurityIndexTrace SecurityMonitorGraphView
  SecurityMonitorIndexTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Collision event in the retained common history, with the actual lifetime cap. -/
def Bad (history : History) : Prop := Conflict history.indexTrace ∧ marks history.indexTrace ≤ LIFETIME

theorem aligned_conflict_le {α : Type} (program : SecurityIndexProgram.Program α) (traceOf : α → List Entry)
    (aligned : Aligned program traceOf []) :
    Pr[fun value => Conflict (traceOf value) ∧ marks (traceOf value) ≤ LIFETIME |
      SecurityMonitorIndexView.observe program] ≤
      expectedValue (SecurityMonitorIndexView.observe program) (fun value => ((traceOf value).length : ENNReal))/2^128 := by
  have bound := SecurityIndexProgram.prob_lifetime_conflict_le program
  have event : Pr[fun result => Conflict (traceOf result.1) ∧ marks (traceOf result.1) ≤ LIFETIME |
      SecurityIndexProgram.execute program] =
      Pr[fun result => Conflict result.2 ∧ marks result.2 ≤ LIFETIME | SecurityIndexProgram.execute program] := by
    apply probEvent_congr' _ rfl
    intro result member
    have same := aligned result member
    simp only [List.nil_append] at same
    rw [same]
  have cost : expectedValue (SecurityIndexProgram.execute program) (fun result => ((traceOf result.1).length : ENNReal)) =
      expectedValue (SecurityIndexProgram.execute program) (fun result => (result.2.length : ENNReal)) := by
    apply expectedValue_congr_of_support
    intro result member
    have same := aligned result member
    simp only [List.nil_append] at same
    rw [same]
  simpa only [SecurityMonitorIndexView.observe, probEvent_map, expectedValue_map, Function.comp_def, event, cost] using bound

/-- A fixed table, nonce function, and metadata leave fresh H5 draws uniform.
The probability and expected trace length refer to the same retained execution. -/
theorem start_bad_le {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) :
    Pr[fun result => Bad result.value.history |
      SecurityGraphMonitorProgram.run table ∅ (SecurityMonitorGraphView.start nonces metadata pk view budget)] ≤
      expectedValue (SecurityGraphMonitorProgram.run table ∅ (SecurityMonitorGraphView.start nonces metadata pk view budget))
        (fun result => (result.value.history.indexTrace.length : ENNReal))/2^128 := by
  have bound := aligned_conflict_le (SecurityMonitorIndexView.start table nonces metadata pk view budget)
    (fun result => result.history.indexTrace) (start_aligned table nonces metadata pk view budget)
  rw [SecurityMonitorIndexView.observe_start] at bound
  simpa only [SecurityGraphMonitorObserve.observe, probEvent_map, expectedValue_map, Function.comp_def, Bad] using bound

theorem setup_bad_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) :
    Pr[fun result => Bad result.value.history |
      SecurityGraphMonitorProgram.experiment (SecurityMonitorGraphView.start nonces metadata pk view budget) ∅] ≤
      expectedValue (SecurityGraphMonitorProgram.experiment (SecurityMonitorGraphView.start nonces metadata pk view budget) ∅)
        (fun result => (result.value.history.indexTrace.length : ENNReal))/2^128 := by
  unfold SecurityGraphMonitorProgram.experiment
  simp only [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ PointTable) (fun table =>
      expectedValue (SecurityGraphMonitorProgram.run (complete ∅ table) ∅
        (SecurityMonitorGraphView.start nonces metadata pk view budget))
        (fun result => (result.value.history.indexTrace.length : ENNReal))/2^128) := by
      apply expectedValue_mono
      intro table
      exact start_bad_le _ _ _ _ _ _
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

/-- Concrete actual-adversary bound in the common passive distribution. -/
theorem experiment_bad_le (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[fun result => Bad result.value.history | SecurityMonitorGraphView.experiment publicCache adversary rounds budget] ≤
      expectedValue (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)
        (fun result => (result.value.history.indexTrace.length : ENNReal))/2^128 := by
  unfold SecurityMonitorGraphView.experiment
  simp only [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ NonceTable) (fun nonces => expectedValue ($ᵗ MetadataTable) (fun metadata =>
      expectedValue (SecurityGraphMonitorProgram.experiment
        (SecurityMonitorGraphView.start nonces metadata (truncate (metadata (.node 151 0)))
          (ofInteract adversary (truncate (metadata (.node 151 0))) rounds
            (adversary.initial (truncate (metadata (.node 151 0))) publicCache) {}) budget) ∅)
        (fun result => (result.value.history.indexTrace.length : ENNReal))/2^128)) := by
      apply expectedValue_mono
      intro nonces
      apply expectedValue_mono
      intro metadata
      exact setup_bad_le nonces metadata _ _ budget
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

#print axioms experiment_bad_le
end SigGolfCandidate.Hypertree.SecurityMonitorIndexBound
