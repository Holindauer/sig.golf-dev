import SigGolfCandidate.Hypertree.SecurityIndexTrace

namespace SigGolfCandidate.Hypertree.SecurityIndexProgram
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityIndexTrace
set_option backward.isDefEq.respectTransparency false

/-- Preserve the final attacker outcome and charged counters while monitoring fresh H5 draws. -/
inductive Program (α : Type) where
  | pure (value : α)
  | draw (mark : Bool) (next : BitVec 256 → Program α)
  | coin (n : Nat) (next : Fin (n+1) → Program α)

def erase {α : Type} : Program α → SecurityIndexMonitor.Strategy
  | .pure _ => .done
  | .draw mark next => .draw mark (fun answer => erase (next answer))
  | .coin n next => .coin n (fun answer => erase (next answer))

noncomputable def execute {α : Type} : Program α → ProbComp (α × List Entry)
  | .pure value => pure (value,[])
  | .draw mark next => do
      let answer ← $ᵗ BitVec 256
      (fun result => (result.1,(mark,answer.extractLsb' 0 160)::result.2)) <$> execute (next answer)
  | .coin n next => do
      let answer ← $ᵗ Fin (n+1)
      execute (next answer)

theorem trace_projection {α : Type} (program : Program α) :
    Prod.snd <$> execute program = trace (erase program) := by
  induction program with
  | pure value => rfl
  | coin n next ih => simp only [execute, erase, trace, map_bind, ih]
  | draw mark next ih =>
    simp only [execute, erase, trace, map_bind, Functor.map_map]
    apply bind_congr
    intro answer
    rw [← ih answer, Functor.map_map]

theorem counter_projection {α : Type} (program : Program α) :
    (fun result => result.2.length) <$> execute program = SecurityIndexMonitor.draws (erase program) := by
  rw [← trace_length, ← trace_projection, Functor.map_map]

theorem prob_conflict_le {α : Type} (program : Program α) (limit : Nat) :
    Pr[fun result => Conflict result.2 ∧ marks result.2 ≤ limit | execute program] ≤
      (limit : ENNReal)/2^160 * expectedValue (execute program) (fun result => (result.2.length : ENNReal)) := by
  have bound := SecurityIndexTrace.prob_conflict_le (erase program) limit
  rw [← trace_projection, probEvent_map, SecurityIndexMonitor.cost_eq_expected,
    ← counter_projection, expectedValue_map] at bound
  exact bound

/-- Joint-output bound: the original result remains available for coupling with the actual game. -/
theorem prob_lifetime_conflict_le {α : Type} (program : Program α) :
    Pr[fun result => Conflict result.2 ∧ marks result.2 ≤ LIFETIME | execute program] ≤
      expectedValue (execute program) (fun result => (result.2.length : ENNReal))/2^128 := by
  have bound := SecurityIndexTrace.prob_lifetime_conflict_le (erase program)
  rw [← trace_projection, probEvent_map, expectedValue_map] at bound
  exact bound

/-- info: 'SigGolfCandidate.Hypertree.SecurityIndexProgram.prob_lifetime_conflict_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prob_lifetime_conflict_le
end SigGolfCandidate.Hypertree.SecurityIndexProgram
