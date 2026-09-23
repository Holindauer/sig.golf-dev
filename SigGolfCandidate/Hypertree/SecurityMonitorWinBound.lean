import SigGolfCandidate.Hypertree.SecurityMonitorWin
import SigGolfCandidate.Hypertree.SecurityMonitorCombined
import SigGolfCandidate.Hypertree.SecurityActualCutoff

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor
  SecurityMonitorIndexState SecurityMonitorIndexContact SecurityMonitorNonceView SecurityMonitorCombined
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

 theorem nonceHit_hits (nonces : NonceTable) (history : History) (hit : NonceHit nonces history) :
    hits nonces history = true := by
  obtain ⟨message, present⟩ := hit
  exact List.any_eq_true.mpr ⟨(message,nonces message), present, by simp⟩

 theorem joint_won_bad (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : JointResult)
    (member : result ∈ support (joint publicCache adversary rounds budget))
    (won : SecurityActualCutoff.Won result.2.value.value) :
    result.2.bad = true ∨ hits result.1 result.2.value.history = true ∨
      SecurityIndexTrace.Conflict result.2.value.history.indexTrace := by
  simp only [joint, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨nonces, _, metadata, _, points, _, outcome, member, same⟩ := member
  cases same
  by_cases bad : outcome.bad = true
  · exact Or.inl bad
  · have clean : outcome.bad = false := Bool.eq_false_iff.mpr bad
    obtain ⟨value, output, won⟩ := won
    have extracted := run_winning_bad (points,nonces,metadata) publicCache adversary rounds budget
      outcome value member clean output won
    rcases extracted with conflict | nonce
    · exact Or.inr (Or.inr conflict)
    · exact Or.inr (Or.inl (nonceHit_hits nonces _ nonce))

attribute [local irreducible] joint SecurityMonitorCombined.experiment

/-- A completed winning outcome in the exact common four-monitor experiment
must trigger one of those same concrete recorded bad events. -/
theorem supported_won_bad (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : SecurityMonitorCombined.Result)
    (member : result ∈ support (SecurityMonitorCombined.experiment publicCache adversary rounds budget))
    (won : SecurityActualCutoff.Won result.value.2.value.value) : SecurityMonitorCombined.Bad result := by
  have bad := @joint_won_bad publicCache adversary rounds budget result.value
    (@SecurityMonitorCombined.supported publicCache adversary rounds budget result member) won
  rcases bad with graph | nonce | index
  · exact Or.inr (Or.inl graph)
  · exact Or.inr (Or.inr (Or.inl nonce))
  · exact Or.inr (Or.inr (Or.inr index))

/-- Concrete winning probability in the common simulation, with the actual
adversary, shared cutoff, setup, signatures, and verifier all instantiated. -/
theorem won_le (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[fun result => SecurityActualCutoff.Won result.value.2.value.value |
      SecurityMonitorCombined.experiment publicCache adversary rounds budget] ≤ (budget : ENNReal)/2^127 := by
  apply le_trans _ (SecurityMonitorCombined.bad_le publicCache adversary rounds budget)
  exact probEvent_mono (fun result member won => @supported_won_bad publicCache adversary rounds budget result member won)

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorWin.won_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms won_le
end SigGolfCandidate.Hypertree.SecurityMonitorWin
