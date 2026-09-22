import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorCompile
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
  SecurityGraphFactor SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- State returned by the concrete public-oracle compiler, retaining both caches. -/
abbrev State := QueryCache PointSpec × QueryCache HashSpec

/-- Compile an arbitrary adaptive public/coin computation. Continuations receive
exactly the monitor oracle's public answer, while all test flags remain private. -/
noncomputable def compile {α : Type} (metadata : MetadataTable) (program : OracleComp World α) :
    State → Program (α × State) :=
  OracleComp.construct
    (fun value state => .done (value, state))
    (fun query _ next state => match query with
      | .inl n => .coin n (fun answer => next answer state)
      | .inr input => SecurityGraphMonitorOracle.publicStep metadata state.1 state.2 input
          (fun answer exposed residual => next answer (exposed, residual))) program

@[simp] theorem compile_pure {α : Type} (metadata : MetadataTable) (value : α) (state : State) :
    compile metadata (pure value) state = .done (value, state) := rfl

@[simp] theorem compile_hash {α : Type} (metadata : MetadataTable) (query : Query)
    (next : BitVec 256 → OracleComp World α) (state : State) :
    compile metadata (liftM (World.query (.inr query)) >>= next) state =
      SecurityGraphMonitorOracle.publicStep metadata state.1 state.2 query
        (fun answer exposed residual => compile metadata (next answer) (exposed, residual)) := rfl

@[simp] theorem compile_coin {α : Type} (metadata : MetadataTable) (n : Nat)
    (next : Fin (n + 1) → OracleComp World α) (state : State) :
    compile metadata (liftM (World.query (.inl n)) >>= next) state =
      .coin n (fun answer => compile metadata (next answer) state) := rfl

/-- The public-query cutoff is enforced on the very path that supplies answers
to the adversary. The remaining budget is part of the retained result. -/
noncomputable def limited {α : Type} (metadata : MetadataTable) (program : OracleComp World α) :
    Nat → State → Program (Option α × Nat × State) :=
  OracleComp.construct
    (fun value remaining state => .done (some value, remaining, state))
    (fun query _ next remaining state => match query with
      | .inl n => .coin n (fun answer => next answer remaining state)
      | .inr input => match remaining with
        | 0 => .done (none, 0, state)
        | remaining + 1 => SecurityGraphMonitorOracle.publicStep metadata state.1 state.2 input
            (fun answer exposed residual => next answer remaining (exposed, residual))) program

/-- A cutoff is an operational bound on the same passive path; no cost is
transferred from another experiment after the first bad event. -/
theorem limited_within {α : Type} (metadata : MetadataTable) (program : OracleComp World α)
    (remaining : Nat) (state : State) :
    Within (2 * remaining) (erase (limited metadata program remaining state)) := by
  induction program using OracleComp.inductionOn generalizing remaining state with
  | pure value => exact Within.done _
  | query_bind query next ih =>
    cases query with
    | inl n => exact Within.coin (fun answer => ih answer remaining state)
    | inr input =>
      cases remaining with
      | zero => exact Within.done _
      | succ remaining =>
        change Within (2 * (remaining + 1))
          (erase (SecurityGraphMonitorOracle.publicStep metadata state.1 state.2 input
            (fun answer exposed residual => limited metadata (next answer) remaining (exposed, residual))))
        rw [SecurityGraphMonitorOracle.erase_publicStep]
        convert SecurityGraphPublicMonitor.publicStep_within metadata state.1 state.2 input
          (fun answer exposed residual => erase (limited metadata (next answer) remaining (exposed, residual)))
          (2 * remaining) (fun answer exposed residual => ih answer remaining (exposed, residual)) using 1 <;> omega

/-- The finite-query compiler inherits the unconditional passive bound, including
arbitrary adaptive coin ranges, malformed queries, and repeated cache lookups. -/
theorem limited_bad_le {α : Type} (metadata : MetadataTable) (program : OracleComp World α)
    (remaining : Nat) (state : State) :
    Pr[fun result => result.bad = true |
      SecurityGraphMonitorProgram.experiment (limited metadata program remaining state) state.1] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := prob_playAll_le (limited_within metadata program remaining state) state.1
  change Pr[fun hit => hit = true | SecurityGraphPassiveCost.fullExperiment
    (erase (limited metadata program remaining state)) state.1] ≤ _ at bound
  rw [← SecurityGraphMonitorProgram.experiment_bad, probEvent_map] at bound
  exact bound

end SigGolfCandidate.Hypertree.SecurityGraphMonitorCompile
