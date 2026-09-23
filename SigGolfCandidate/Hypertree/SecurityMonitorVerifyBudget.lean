import SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorVerify

namespace SigGolfCandidate.Hypertree.SecurityMonitorVerifyBudget
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorCompose SecurityMonitorView SecurityMonitorIndexState
  SecurityMonitorGraphState SecurityMonitorGraphStoppedView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
attribute [local irreducible] recordParsed

/-- A completed budgeted hash-only phase is an actual completed raw verifier
run. Budget failures and graph contacts cannot supply a completed value. -/
theorem completed {α β : Type} (factors : Factors) (pk : PublicKey) (program : OracleComp HashSpec α)
    (finish : α → β) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) (ready : Ready factors history exposed cache)
    (result : SecurityMonitorGraphView.Result β)
    (member : some result ∈ support (execute factors pk
      (ofHash program (fun value => .done (finish value))) remaining exposed cache history))
    (finished : result.value ≠ none) :
    ∃ value, result.value = some (finish value) ∧
      some (value,result.exposed,result.residual) ∈ support (stopped factors.1 exposed
        (SecurityGraphMonitorVerify.compile factors.2.2 program exposed cache)) ∧
      result.history.signedMessages = history.signedMessages ∧
      result.history.signedIndices = history.signedIndices := by
  induction program using OracleComp.inductionOn generalizing remaining exposed cache history with
  | pure value =>
    simp only [ofHash_pure, execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    refine ⟨value, rfl, ?_, rfl, rfl⟩
    simp only [SecurityGraphMonitorVerify.compile_pure, stopped, support_pure, Set.mem_singleton_iff]
  | query_bind query next ih =>
    rw [ofHash_query] at member
    cases remaining with
    | zero =>
      simp only [execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact False.elim (finished rfl)
    | succ remaining =>
      rw [execute] at member
      by_cases first : SecurityGraphMonitorPublicCoupling.inputHit factors exposed query
      · simp only [if_pos first, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
      · rw [if_neg first, mem_support_bind_iff] at member
        obtain ⟨answer, queried, tail⟩ := member
        by_cases second : SecurityGraphMonitorPublicCoupling.outputHit factors query answer.1
        · simp only [if_pos second, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
        · rw [if_neg second] at tail
          have read := read_supported factors history exposed cache ready query answer queried first second
          have nextReady := public_ready factors pk history exposed cache ready query _ read
          obtain ⟨value, output, raw, messages, indices⟩ := ih answer.1 remaining _ answer.2 _ nextReady tail
          refine ⟨value, output, ?_, ?_, ?_⟩
          · rw [SecurityGraphMonitorVerify.compile_query,
              stopped_public_bind factors history.signedIndices exposed cache ready.1,
              mem_support_bind_iff]
            exact ⟨some (answer.1, SecurityGraphMonitorPublicCoupling.opened factors exposed query, answer.2), read, raw⟩
          · simpa only [public_messages] using messages
          · simpa only [public_indices] using indices

#print axioms completed
end SigGolfCandidate.Hypertree.SecurityMonitorVerifyBudget
