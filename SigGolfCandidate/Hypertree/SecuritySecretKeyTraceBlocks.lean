import SigGolfCandidate.Hypertree.SecuritySecretKeyHonestSign

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyTraceBlocks
open SigGolf OracleComp OracleSpec SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityBudget SecurityAtomicCutoff SecuritySecretKeyHonest
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- A query that never contributes to the public secret key-guess log. -/
def clean : GameWorld.Domain → Prop
  | .inl _ => True
  | .inr input => allowed input

theorem clean_prepend (input : GameWorld.Domain) (good : clean input) (inputs : List Query) :
    prependPublic input inputs = inputs := by
  cases input with
  | inl n => rfl
  | inr input =>
    cases input with
    | inl slot => rfl
    | inr query => exact if_neg good

theorem lift_clean {α : Type} {program : OracleComp SplitWorld α} (safe : Safe allowed program) :
    Safe clean (program.liftComp GameWorld) := by
  induction safe with
  | pure value => exact Safe.pure _
  | query input next good safe ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change Safe clean (liftM (GameWorld.query (.inr input)) >>= _)
    exact Safe.query _ _ good ih

/-- A safe prefix emits no secret key-input entries, while retaining every later
entry and the full continuation output. -/
theorem trace_bind {α β : Type} {program : OracleComp GameWorld α} (safe : Safe clean program)
    (next : α → OracleComp GameWorld β) :
    tracePublic (program >>= next) = (program >>= fun value => tracePublic (next value)) := by
  induction safe with
  | pure value => simp only [pure_bind]
  | query input continuation good safe ih =>
    rw [bind_assoc, tracePublic_query_bind, bind_assoc]
    apply bind_congr
    intro answer
    rw [ih answer]
    simp only [clean_prepend input good, bind_assoc, Prod.mk.eta, bind_pure]

/-- Metering may stop a safe block early but cannot introduce a secret key input. -/
theorem metered_clean {α : Type} {program : OracleComp GameWorld α} (safe : Safe clean program) (budget : Nat) :
    Safe clean (metered program budget) := by
  induction safe generalizing budget with
  | pure value => exact Safe.pure _
  | query input next good safe ih =>
    rw [metered_query_bind]
    split
    · exact Safe.query input _ good (fun answer => ih answer _)
    · exact Safe.pure _

/-- The cutoff continuation receives the unspent budget of the prefix. -/
theorem cutoff_bind {α β : Type} (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld β) (budget : Nat) :
    cutoff (program >>= next) budget = (do
      let result ← metered program budget
      match result with
      | none => pure none
      | some (value, remaining) => cutoff (next value) remaining) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, cutoff_query_bind, metered_query_bind]
    split
    · simp only [bind_assoc, ih]
    · simp

/-- No eligible public input is produced even by an honest prefix that later
runs out of budget. Aborted execution retains its ordinary `none` output. -/
theorem trace_cutoff_bind {α β : Type} {program : OracleComp GameWorld α} (safe : Safe clean program)
    (next : α → OracleComp GameWorld β) (budget : Nat) :
    tracePublic (cutoff (program >>= next) budget) = (do
      let result ← metered program budget
      match result with
      | none => pure (none, [])
      | some (value, remaining) => tracePublic (cutoff (next value) remaining)) := by
  rw [cutoff_bind, trace_bind (metered_clean safe budget)]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some pair => cases pair; rfl

theorem metered_insufficient {α : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (budget : Nat) (short : budget < cost)
    (result : Option (α × Nat)) (member : result ∈ support (metered program budget)) : result = none := by
  induction fixed generalizing budget with
  | pure value => omega
  | query input next cost fixed ih =>
    rw [metered_query_bind] at member
    split at member
    next enough =>
      rw [mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer _ (by omega) member
    next exhausted => simpa using member

/-- Sufficient budget preserves the honest block and debits its exact cost,
while all secret key-log entries come from its continuation. -/
theorem trace_enough {α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (safe : Safe clean program) (fixed : FixedCost program cost)
    (next : α → OracleComp GameWorld β) (budget : Nat) (enough : cost ≤ budget) :
    tracePublic (cutoff (program >>= next) budget) =
      (program >>= fun value => tracePublic (cutoff (next value) (budget - cost))) := by
  rw [fixed.bind_enough next budget enough, trace_bind safe]

/-- Insufficient honest-block budget has exactly the ordinary budget-abort
output and empty secret key log, under any stateful probabilistic oracle. -/
theorem trace_insufficient {σ α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (safe : Safe clean program) (fixed : FixedCost program cost)
    (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (next : α → OracleComp GameWorld β) (budget : Nat) (cache : σ) (short : budget < cost) :
    𝒮[(simulateQ implementation (tracePublic (cutoff (program >>= next) budget))).run' cache] =
      𝒮[(pure (none, []) : ProbComp (Option β × List Query))] := by
  rw [trace_cutoff_bind safe]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  let first := (simulateQ implementation (metered program budget)).run cache
  have step (result : Option (α × Nat) × σ) (member : result ∈ support first) : result.1 = none := by
    apply metered_insufficient fixed budget short result.1
    apply support_simulateQ_run'_subset implementation _ cache
    rw [StateT.run'_eq, support_map]
    exact ⟨result, member, rfl⟩
  calc
    _ = 𝒮[(fun _ => (none, [])) <$> first] := by
      simp only [map_eq_pure_bind]
      apply evalSPMF_bind_congr
      intro result member
      rw [step result member]
      simp
    _ = _ := by
      classical
      let : DecidableEq (Option β × List Query) := Classical.decEq _
      apply evalSPMF_ext
      intro result
      simp only [map_eq_pure_bind, probOutput_bind_const]
      simp

end SigGolfCandidate.Hypertree.SecuritySecretKeyTraceBlocks
