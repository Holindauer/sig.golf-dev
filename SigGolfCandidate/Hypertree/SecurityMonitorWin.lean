import SigGolfCandidate.Hypertree.SecurityMonitorWinInteraction
import SigGolfCandidate.Hypertree.SecurityMonitorResidual

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorPublicCoupling
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
  SecurityMonitorGraphStoppedView SecurityMonitorIndexContact SecurityGraphExtraction SecurityMonitorTranscript
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

 theorem checker_bad (factors : Factors) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (tracked : Tracked factors.2.1 (publicKey factors) cache history)
    (result : Result SecurityExperiment.Result) (outcome : SecurityExperiment.Result)
    (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors (publicKey factors)
      (ofCheck (publicKey factors) transcript forgery) remaining exposed cache history)) :
    SecurityIndexTrace.Conflict result.history.indexTrace ∨ NonceHit factors.2.1 result.history := by
  let base := completion result.residual
  have agree := completion_agrees result.residual
  obtain ⟨reuse, honest, messages, raw⟩ := check_reuse factors transcript forgery remaining exposed cache history
    ready coherent result outcome output won member base agree
  have replay := SecurityGraphMonitorVerify.completed factors history.signedIndices _ exposed cache ready.1
    (true,result.exposed,result.residual) raw base agree
  have publicAgree := SecurityMonitorResidual.agrees_public factors result.residual replay.2.2.1.2.2 base agree
  have present := SecurityMonitorResidual.verifier_index_present factors history.signedIndices (publicKey factors)
    (candidate forgery).1 (candidate forgery).2 exposed cache ready.1
    (true,result.exposed,result.residual) raw
  have finalTracked := execute_tracked factors (publicKey factors) _ (ofCheck_wellFormed _ transcript forgery)
    remaining exposed cache history tracked result member
  obtain ⟨draws, provenance⟩ := finalTracked.2.2
  exact extraction_contact factors base (responses transcript) result.history result.residual draws
    provenance honest messages publicAgree (candidate forgery).1 (candidate forgery).2 present reuse

/-- All state and transcript premises are propagated through the actual finite
adversary interaction before applying the final checker extraction. -/
theorem interaction_bad (factors : Factors) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (tracked : Tracked factors.2.1 (publicKey factors) cache history)
    (result : Result SecurityExperiment.Result) (outcome : SecurityExperiment.Result)
    (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors (publicKey factors)
      (ofInteract adversary (publicKey factors) rounds state transcript) remaining exposed cache history)) :
    SecurityIndexTrace.Conflict result.history.indexTrace ∨ NonceHit factors.2.1 result.history := by
  obtain ⟨transcript, forgery, remaining, exposed, cache, history, ready, coherent, tracked, member⟩ :=
    interact_atChecker factors adversary rounds state transcript remaining exposed cache history ready coherent tracked
      result outcome output won member
  exact checker_bad factors transcript forgery remaining exposed cache history ready coherent tracked
    result outcome output won member

/-- Concrete deterministic winning-outcome bridge for the common passive
simulation. Setup, all honest responses, and final verification are actual code.
Only the already-recorded index conflict or prereveal nonce hit can remain once
the actual graph-contact flag is false. -/
theorem run_winning_bad (factors : Factors) (publicCache : Cache)
    (adversary : Adversary submission.sizes) (rounds budget : Nat)
    (result : Outcome (Result SecurityExperiment.Result)) (outcome : SecurityExperiment.Result)
    (member : result ∈ support (run factors.1 ∅
      (start factors.2.1 factors.2.2 (publicKey factors)
        (ofInteract adversary (publicKey factors) rounds (adversary.initial (publicKey factors) publicCache) {}) budget)))
    (clean : result.bad = false) (output : result.value.value = some outcome) (won : outcome.won = true) :
    SecurityIndexTrace.Conflict result.value.history.indexTrace ∨ NonceHit factors.2.1 result.value.history := by
  have stoppedMember : some result.value ∈ support (stopped factors.1 ∅
      (start factors.2.1 factors.2.2 (publicKey factors)
        (ofInteract adversary (publicKey factors) rounds (adversary.initial (publicKey factors) publicCache) {}) budget)) := by
    apply (mem_support_iff_of_evalSPMF_eq (stopped_eq factors.1 ∅ _) (some result.value)).mpr
    rw [support_map]
    exact ⟨result, member, by simp only [keep, clean, Bool.false_eq_true, if_false]⟩
  rw [start] at stoppedMember
  by_cases enough : 739 ≤ budget
  · rw [if_pos enough, SecurityGraphMonitorSetup.setup, SecurityGraphMonitorMetadata.stopped_disclose] at stoppedMember
    have executed := (mem_support_iff_of_evalSPMF_eq
      (stopped_compile factors (publicKey factors) _ (budget - 739) _ ∅ _ (setup_ready factors))
      (some result.value)).mp stoppedMember
    exact interaction_bad factors adversary rounds _ {} (budget - 739) _ ∅ _ (setup_ready factors)
      (coherent_empty factors) (tracked_empty factors.2.1 (publicKey factors)).keygen
      result.value outcome output won executed
  · simp only [if_neg enough, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at stoppedMember
    rw [stoppedMember] at output
    cases output

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorWin.run_winning_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_winning_bad
end SigGolfCandidate.Hypertree.SecurityMonitorWin
