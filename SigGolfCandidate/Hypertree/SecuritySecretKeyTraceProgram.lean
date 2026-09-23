import SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphFactor SecurityGraphPassive
  SecurityBudget SecuritySecretKeyTraceBlocks SecurityMonitorViewAtomic SecurityGraphState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem keygen_run (factors : Factors) (cache : QueryCache HashSpec) :
    (simulateQ (handler factors) (SecurityIdealKeygen.keygen.liftComp GameWorld)).run cache =
      pure (truncate (factors.2.2 (.node 151 0)), cache) := by
  rw [handler, routing, routed_keygen_run, labels_node]

/-- Actual key generation followed by the actual adversary program has exactly
the true graph interpreter's output and secret key-input log at every total-call
cutoff. Ordinary budget exhaustion remains `none` with its retained trace. -/
theorem traced_program (factors : Factors) (publicCache : SigGolf.Cache)
    (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    𝒮[traced factors (SecurityExperiment.program publicCache adversary rounds) budget ∅] =
      𝒮[project <$> SecurityMonitorGraphCoupling.start factors (truncate (factors.2.2 (.node 151 0)))
        (ofInteract adversary (truncate (factors.2.2 (.node 151 0))) rounds
          (adversary.initial (truncate (factors.2.2 (.node 151 0))) publicCache) {}) budget] := by
  have safe := lift_clean SecuritySecretKeyHonest.keygen
  have fixed := SecurityAtomicCounts.keygen
  rw [traced, SecurityMonitorView.program_eq, SecurityMonitorGraphCoupling.start]
  by_cases enough : 739 ≤ budget
  · rw [if_pos enough, trace_enough safe fixed _ budget enough, run_bind, keygen_run, pure_bind]
    have same := traced_view factors (truncate (factors.2.2 (.node 151 0)))
      (ofInteract adversary (truncate (factors.2.2 (.node 151 0))) rounds
        (adversary.initial (truncate (factors.2.2 (.node 151 0))) publicCache) {})
      (budget - 739) (SecurityGraphMonitorSetup.cache factors.1 factors.2.2) ∅ (recordKeygen {})
    have identity : extend (α := SecurityExperiment.Result) (recordKeygen {}) = id := by
      funext result
      rcases result with ⟨value, inputs⟩
      rfl
    simpa only [identity, id_map, traced] using same
  · rw [if_neg enough, trace_insufficient safe fixed (handler factors) _ budget ∅ (by omega)]
    rfl

/-- The equivalent presentation at the existing private-fixing/graph-oracle
interface makes the theorem directly usable by factor presampling. -/
theorem routed_traced_program (factors : Factors) (publicCache : SigGolf.Cache)
    (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    𝒮[(simulateQ (SecurityGraphOracle.implementation (privateTable factors) (labels factors))
      (SecurityGraphIdeal.fixPrivate (privateTable factors)
        (tracePublic (cutoff (SecurityExperiment.program publicCache adversary rounds) budget)))).run' ∅] =
      𝒮[project <$> SecurityMonitorGraphCoupling.start factors (truncate (factors.2.2 (.node 151 0)))
        (ofInteract adversary (truncate (factors.2.2 (.node 151 0))) rounds
          (adversary.initial (truncate (factors.2.2 (.node 151 0))) publicCache) {}) budget] := by
  rw [←routing]
  exact traced_program factors publicCache adversary rounds budget

/-- Trace order cannot affect whether a secret key was guessed. -/
theorem secretKeyHit_reverse (inputs : List Query) (secretKey : SecretKey) :
    SecuritySecretKey.SecretKeyHitTrace inputs.reverse secretKey ↔ SecuritySecretKey.SecretKeyHitTrace inputs secretKey := by
  simp only [SecuritySecretKey.SecretKeyHitTrace, List.mem_reverse]

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView.routed_traced_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms routed_traced_program
end SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
