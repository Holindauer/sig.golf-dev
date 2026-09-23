import SigGolfCandidate.Hypertree.SecurityMonitorWinCoherence
import SigGolfCandidate.Hypertree.SecurityMonitorVerifyBudget

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityGraphFactor
  SecurityGraphReference SecurityGraphSigner SecurityGraphExtraction SecurityGraphMonitorCompose
  SecurityMonitorIndexState SecurityMonitorTranscript SecurityMonitorIndexContact
  SecurityGraphPassive SecurityGraphMonitorProgram SecurityMonitorGraphState
  SecurityMonitorView SecurityMonitorGraphStoppedView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A deterministic total extension suffices; no additional oracle sample is
assumed when extracting a completed finite execution. -/
noncomputable def completion (cache : QueryCache HashSpec) : Hash := fun query => (cache query).getD 0

theorem completion_agrees (cache : QueryCache HashSpec) : cache.AgreesWithFn (completion cache) := by
  intro query answer present
  simp only [completion, present, Option.getD_some]

 theorem honest_ideal (factors : Factors) (base : Hash) (responses : SecurityForgery.History)
    (honest : HonestHistory factors base responses) :
    ∀ entry ∈ responses, entry.2 = evalWithAnswerFn
      (answers (privateTable factors) (programmed (privateTable factors) (labels factors) base))
      (SecurityIdealSign.signCompact (publicKey factors) entry.1) := by
  intro entry member
  rw [eval_signCompact, honest entry member, index_residual]

/-- A winning completed organizer checker has a fresh decoded forgery and
an actual index reuse. Its whole verifier ran within the common budget. -/
theorem check_reuse (factors : Factors) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (result : SecurityMonitorGraphView.Result SecurityExperiment.Result)
    (outcome : SecurityExperiment.Result) (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors (publicKey factors)
      (ofCheck (publicKey factors) transcript forgery) remaining exposed cache history))
    (base : Hash) (agree : result.residual.AgreesWithFn base) :
    IndexReuse factors base (responses transcript) (candidate forgery).1 (candidate forgery).2 ∧
      HonestHistory factors base (responses transcript) ∧
      (∀ entry ∈ responses transcript, entry.1 ∈ result.history.signedMessages) ∧
      some (true,result.exposed,result.residual) ∈ support (stopped factors.1 exposed
        (SecurityGraphMonitorVerify.compile factors.2.2
          (SecurityVerify.verifyCompact (publicKey factors) (candidate forgery).1 (candidate forgery).2) exposed cache)) := by
  rw [ofCheck_eq] at member
  obtain ⟨accepted, resultEq, raw, messages, indices⟩ := SecurityMonitorVerifyBudget.completed
    factors (publicKey factors) _ _ remaining exposed cache history ready result member
    (by rw [output]; exact Option.some_ne_none _)
  have outcomeEq := Option.some.inj (output.symm.trans resultEq)
  have win : (accepted && fresh transcript forgery) = true := by simpa only [outcomeEq] using won
  have acceptedTrue := (Bool.and_eq_true_iff.mp win).1
  have freshTrue := (Bool.and_eq_true_iff.mp win).2
  subst accepted
  have replay := SecurityGraphMonitorVerify.completed factors history.signedIndices _ exposed cache ready.1
    (true,result.exposed,result.residual) raw base agree
  have initial := coherent.2 base replay.1
  have safe : SecurityGraphMonitorChainState.Safe factors (Signed factors base (responses transcript)) exposed cache := by
    rw [← initial.2]
    exact ready.1
  refine ⟨SecurityGraphMonitorVerify.accepted_fresh_index_reuse factors base (responses transcript)
    (honest_ideal factors base _ initial.1) (candidate forgery).1 (candidate forgery).2
    (fresh_candidate transcript forgery freshTrue) exposed cache safe
    (true,result.exposed,result.residual) raw agree rfl, initial.1, ?_, raw⟩
  intro entry present
  rw [messages]
  exact coherent.1 entry present

end SigGolfCandidate.Hypertree.SecurityMonitorWin
