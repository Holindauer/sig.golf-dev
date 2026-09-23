import SigGolfCandidate.Hypertree.SecurityAtomicCutoff

namespace SigGolfCandidate.Hypertree.SecurityAtomicCutoff
open SigGolf OracleComp OracleSpec SecurityGameHop SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A too-expensive initial block prevents every continuation from completing.
No assumption is imposed on the continuation's own cost or control flow. -/
theorem FixedCost.bind_insufficient {α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (next : α → OracleComp GameWorld β)
    (budget : Nat) (short : budget < cost) (result : Option β)
    (member : result ∈ support (cutoff (program >>= next) budget)) : result = none := by
  induction fixed generalizing budget with
  | pure value => omega
  | query input continuation cost fixed ih =>
    rw [bind_assoc, cutoff_query_bind] at member
    split at member
    next allowed =>
      rw [mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer (budget - charge input) (by omega) member
    next exhausted => simpa using member

/-- The sufficient-budget identity preserves state as well as outputs under any
stateful probabilistic implementation. -/
theorem FixedCost.run_bind_enough {σ α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (next : α → OracleComp GameWorld β) (state : σ) (budget : Nat) (enough : cost ≤ budget) :
    (simulateQ implementation (cutoff (program >>= next) budget)).run state =
      ((simulateQ implementation program).run state >>= fun first =>
        (simulateQ implementation (cutoff (next first.1) (budget - cost))).run first.2) := by
  rw [fixed.bind_enough next budget enough, simulateQ_bind, StateT.run_bind]

/-- Every successful-result event has probability zero after an insufficient
honest block, including for an implementation that can fail internally. -/
theorem FixedCost.prob_bind_insufficient {σ α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (next : α → OracleComp GameWorld β) (state : σ) (budget : Nat) (short : budget < cost)
    (event : β → Prop) :
    Pr[fun result => ∃ value, result = some value ∧ event value |
      (simulateQ implementation (cutoff (program >>= next) budget)).run' state] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro result member
  have stopped := fixed.bind_insufficient next budget short result
    (OracleComp.support_simulateQ_run'_subset implementation _ state member)
  simp [stopped]

/-- Atomic abort is exact for terminal outputs when the oracle never fails.
This does not assert equality of the hidden state left by the aborted prefix. -/
theorem FixedCost.run_bind_insufficient {σ α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (next : α → OracleComp GameWorld β) (state : σ) (budget : Nat) (short : budget < cost)
    (noFailure : Pr[⊥ | (simulateQ implementation (cutoff (program >>= next) budget)).run' state] = 0) :
    𝒮[(simulateQ implementation (cutoff (program >>= next) budget)).run' state] =
      𝒮[(Pure.pure (none : Option β) : ProbComp (Option β))] := by
  have allNone : ∀ result ∈ support ((simulateQ implementation (cutoff (program >>= next) budget)).run' state),
      result = none := fun result member => fixed.bind_insufficient next budget short result
        (OracleComp.support_simulateQ_run'_subset implementation _ state member)
  apply evalSPMF_ext
  intro result
  cases result with
  | none =>
    simpa using (probOutput_eq_one_iff_forall _ none).mpr ⟨noFailure, allNone⟩
  | some value =>
    have zero : Pr[= some value | (simulateQ implementation (cutoff (program >>= next) budget)).run' state] = 0 := by
      apply (probOutput_eq_zero_iff _ _).mpr
      intro member
      cases allNone (some value) member
    rw [zero]
    simp

/-- Full atomic scheduling rule: sufficient budget executes the block and debits
its exact charge; insufficient budget terminates with `none`. -/
theorem FixedCost.atomic_run {σ α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (next : α → OracleComp GameWorld β) (state : σ) (budget : Nat)
    (noFailure : Pr[⊥ | (simulateQ implementation (cutoff (program >>= next) budget)).run' state] = 0) :
    𝒮[(simulateQ implementation (cutoff (program >>= next) budget)).run' state] =
      if cost ≤ budget then
        𝒮[(simulateQ implementation (do
          let value ← program
          cutoff (next value) (budget - cost))).run' state]
      else 𝒮[(Pure.pure (none : Option β) : ProbComp (Option β))] := by
  split
  next enough => rw [fixed.bind_enough next budget enough]
  next short => exact fixed.run_bind_insufficient implementation next state budget (by omega) noFailure

/-- The actual ideal game oracle satisfies the atomic scheduling rule without
any additional no-failure hypothesis. -/
theorem FixedCost.ideal_atomic_run {α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (next : α → OracleComp GameWorld β)
    (state : SecuritySeparation.SplitCache) (budget : Nat) :
    𝒮[(simulateQ idealGameOracle (cutoff (program >>= next) budget)).run' state] =
      if cost ≤ budget then
        𝒮[(simulateQ idealGameOracle (do
          let value ← program
          cutoff (next value) (budget - cost))).run' state]
      else 𝒮[(Pure.pure (none : Option β) : ProbComp (Option β))] := by
  apply fixed.atomic_run idealGameOracle next state budget
  simp

/-- info: 'SigGolfCandidate.Hypertree.SecurityAtomicCutoff.FixedCost.atomic_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedCost.atomic_run
end SigGolfCandidate.Hypertree.SecurityAtomicCutoff
