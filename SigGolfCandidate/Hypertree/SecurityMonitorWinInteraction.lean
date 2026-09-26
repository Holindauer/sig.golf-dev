import SigGolfCandidate.Hypertree.SecurityMonitorWinCheck

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorPublicCoupling
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
  SecurityMonitorGraphStoppedView SecurityMonitorIndexContact SecurityGraphExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A genuine final checking phase, with all state invariants established from
the actual preceding interaction rather than postulated for its transcript. -/
def AtChecker (factors : Factors) (result : Result SecurityExperiment.Result) : Prop :=
  ∃ transcript forgery remaining exposed cache history,
    Ready factors history exposed cache ∧ Coherent factors cache history transcript ∧
    Tracked factors.2.1 (publicKey factors) cache history ∧
    some result ∈ support (execute factors (publicKey factors)
      (ofCheck (publicKey factors) transcript forgery) remaining exposed cache history)

 theorem done_loses (factors : Factors) (pk : PublicKey) (value : SecurityExperiment.Result)
    (lost : value.won = false) (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History) (result : Result SecurityExperiment.Result)
    (outcome : SecurityExperiment.Result) (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors pk (.done value) remaining exposed cache history)) : False := by
  simp only [execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
  cases member
  have same := Option.some.inj output
  rw [← same, lost] at won
  cases won

/-- Every winning finite interaction really reaches the final verifier, with
honest response history and exact tracked oracle state, under both submit modes. -/
theorem interact_atChecker (factors : Factors) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (tracked : Tracked factors.2.1 (publicKey factors) cache history)
    (result : Result SecurityExperiment.Result) (outcome : SecurityExperiment.Result)
    (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors (publicKey factors)
      (ofInteract adversary (publicKey factors) rounds state transcript) remaining exposed cache history)) :
    AtChecker factors result := by
  induction rounds generalizing state transcript remaining exposed cache history with
  | zero => exact False.elim (done_loses factors _ _ rfl remaining exposed cache history result outcome output won member)
  | succ rounds ih =>
    rw [ofInteract] at member
    cases action : adversary.step state with
    | submit forgery =>
      rw [action] at member
      exact ⟨transcript, forgery, remaining, exposed, cache, history, ready, coherent, tracked, member⟩
    | step next =>
      rw [action] at member
      exact ih next transcript remaining exposed cache history ready coherent tracked member
    | sample n resume =>
      simp only [action, execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih (resume answer) transcript remaining exposed cache history ready coherent tracked member
    | hash query resume =>
      rw [action] at member
      cases remaining with
      | zero =>
        simp only [execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
        cases member
        cases output
      | succ remaining =>
        rw [execute] at member
        by_cases first : inputHit factors exposed query
        · simp only [if_pos first, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
        · rw [if_neg first, mem_support_bind_iff] at member
          obtain ⟨answer, queried, member⟩ := member
          by_cases second : outputHit factors query answer.1
          · simp only [if_pos second, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
          · rw [if_neg second] at member
            have read := read_supported factors history exposed cache ready query answer queried first second
            exact ih (resume answer.1) transcript remaining _ answer.2 _
              (public_ready factors _ history exposed cache ready query _ read)
              (coherent.public query answer.1 answer.2 queried)
              (tracked.public_oracle _ _ query answer.1 answer.2 queried) member
    | sign request resume =>
      rw [action] at member
      dsimp only at member
      by_cases allowed : transcript.signingRequests < LIFETIME
      · rw [if_pos allowed, execute] at member
        by_cases enough : 117508 ≤ remaining
        · rw [if_pos enough, mem_support_bind_iff] at member
          obtain ⟨answer, queried, member⟩ := member
          exact ih (resume _) _ (remaining - 117508) _ answer.2 _
            (sign_ready factors history exposed cache ready _ request.message answer.1 answer.2 queried)
            (coherent.sign request.message answer.1 answer.2 queried)
            (tracked.sign_random request.message answer.1 answer.2 queried) member
        · simp only [if_neg enough, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
          cases member
          cases output
      · rw [if_neg allowed] at member
        exact False.elim (done_loses factors _ _ rfl remaining exposed cache history result outcome output won member)

end SigGolfCandidate.Hypertree.SecurityMonitorWin
