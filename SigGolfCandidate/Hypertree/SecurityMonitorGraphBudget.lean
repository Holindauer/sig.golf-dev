import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorReturns

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphBudget
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityMonitorView SecurityMonitorIndexState
  SecurityMonitorGraphView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

theorem returns_mono {α : Type} (program : Program α) (first second : α → Prop)
    (implies : ∀ value, first value → second value) (all : AllReturns first program) :
    AllReturns second program := by
  induction program with
  | done value => exact implies value all
  | guess point value next ih => exact ih all
  | reveal point next ih | coin n next ih | bits next ih | collision target next ih =>
    exact fun answer => ih answer (all answer)

theorem indexStep_returns {α : Type} (property : α → Prop) (cache : QueryCache HashSpec)
    (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α)
    (all : ∀ answer residual, AllReturns property (next answer residual)) :
    AllReturns property (indexStep cache query next) := by
  unfold indexStep
  cases cache query with
  | some answer => exact all answer cache
  | none => exact fun answer => all answer _

/-- Exact conservation on every passive path. The equality also holds after
contacts: monitors never feed their flags back into public control flow. -/
theorem compile_conserved {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) :
    AllReturns (fun result : Result α => result.history.counts.total + result.remaining =
      history.counts.total + remaining) (compile nonces metadata pk view remaining exposed cache history) := by
  induction view generalizing remaining exposed cache history with
  | done value => exact rfl
  | coin n next ih => exact fun answer => ih answer remaining exposed cache history
  | hash query next ih =>
    cases remaining with
    | zero => exact rfl
    | succ remaining =>
      apply publicStep_returns
      intro answer opened residual
      apply returns_mono _ _ _ _ (ih answer remaining opened residual (recordPublic pk history query (cache query).isSome answer))
      intro result conserved
      rw [public_total] at conserved
      omega
  | sign signPk message next ih =>
    unfold compile
    split
    next enough =>
      apply indexStep_returns
      intro answer residual
      apply disclose_returns
      intro opened
      apply returns_mono _ _ _ _ (ih _ (remaining - 111596) opened residual
        (recordSign history message (cache (SecurityRandomOracle.indexInput signPk message (nonces message))).isSome answer))
      intro result conserved
      rw [sign_total] at conserved
      omega
    next short => exact rfl

/-- Setup's 739 calls share the same conserved budget as the full adversary view. -/
theorem start_conserved {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (budget : Nat) :
    AllReturns (fun result : Result α => result.history.counts.total + result.remaining = budget)
      (start nonces metadata pk view budget) := by
  unfold start
  split
  next enough =>
    apply disclose_returns
    intro exposed
    apply returns_mono _ _ _ _ (compile_conserved nonces metadata pk view (budget - 739) exposed ∅ (recordKeygen {}))
    intro result conserved
    rw [keygen_total] at conserved
    change result.history.counts.total + result.remaining = (0 + 739) + (budget - 739) at conserved
    omega
  next short =>
    change 0 + budget = budget
    omega

/-- Support-wise charged-call bound in the same uniform point-table experiment
used by the graph hazard bound. No expectation changes worlds here. -/
theorem start_count_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (budget : Nat) (result : Outcome (Result α))
    (member : result ∈ support (SecurityGraphMonitorProgram.experiment (start nonces metadata pk view budget) ∅)) :
    result.value.history.counts.total ≤ budget := by
  rw [SecurityGraphMonitorProgram.experiment, mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  have conserved := run_returns _ _ (start_conserved nonces metadata pk view budget) _ _ result member
  omega

/-- The actual common passive experiment satisfies the organizer's shared total
H-call cutoff on every path, across setup, signing, public probes, and verification. -/
theorem experiment_count_le (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : Outcome (Result SecurityExperiment.Result))
    (member : result ∈ support (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)) :
    result.value.history.counts.total ≤ budget := by
  unfold SecurityMonitorGraphView.experiment at member
  rw [mem_support_bind_iff] at member
  obtain ⟨nonces, _, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨metadata, _, member⟩ := member
  exact start_count_le nonces metadata _ _ budget result member

end SigGolfCandidate.Hypertree.SecurityMonitorGraphBudget
