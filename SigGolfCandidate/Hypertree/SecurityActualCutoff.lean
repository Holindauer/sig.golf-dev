import SigGolfCandidate.Hypertree.SecurityBytecodeAdapter

namespace SigGolfCandidate.Hypertree.SecurityActualCutoff
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Budget exhaustion is an ordinary failed outcome, not a cryptographic bad event. -/
noncomputable def experiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp (Option SecurityExperiment.Result) := do
  let secretKey ← sampleSecretKey
  (simulateQ (realGameOracle secretKey)
    (SecurityBudget.cutoff (SecurityExperiment.program publicCache adversary rounds) budget)).run' ∅

def Won (value : Option SecurityExperiment.Result) : Prop :=
  ∃ result, value = some result ∧ result.won = true

/-- Exact event equivalence: the cutoff counts honest setup, signing, public
queries, and final verification with the reference game's proved call charges. -/
theorem reference_probability (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[Won | experiment publicCache adversary rounds budget] =
      Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
        SecurityExperiment.realExperiment publicCache adversary rounds] := by
  unfold experiment SecurityExperiment.realExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro secretKey
  congr 1
  unfold Won
  rw [SecurityBudget.prob_cutoff_eq_counted (realGameOracle secretKey)
    (SecurityExperiment.program publicCache adversary rounds) ∅ budget (fun result => result.won = true)]
  simp only [probEvent_map, Function.comp_def]

/-- The real submission's bytecode security event is precisely the completed
winning event of this total-call-cutoff experiment. -/
theorem actual_probability (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      submission.securityExperiment adversary rounds] =
      Pr[Won | experiment KeygenFunctional.zeroCache adversary rounds budget] := by
  rw [SecurityBytecodeAdapter.probability_eq, reference_probability]

#print axioms actual_probability
end SigGolfCandidate.Hypertree.SecurityActualCutoff
