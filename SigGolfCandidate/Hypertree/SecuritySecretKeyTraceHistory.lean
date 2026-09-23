import SigGolfCandidate.Hypertree.SecuritySecretKeyTraceBlocks
import SigGolfCandidate.Hypertree.SecurityMonitorGraphCoupling
import SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphFactor SecurityGraphPassive
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical
attribute [local irreducible] SecurityIndexQuery.parse

private theorem parsed_secretKeyInputs (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (eligible cached : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed eligible cached answer).secretKeyInputs =
      match parsed with
      | some _ => history.secretKeyInputs
      | none => if eligible then query :: history.secretKeyInputs else history.secretKeyInputs := by
  cases parsed with
  | none => cases eligible <;> rfl
  | some pair => cases pair; rfl

/-- Parsed index inputs cannot be secret key inputs. Consequently this recorded
history contains exactly the eligible public-query trace, in reverse order. -/
theorem public_secretKeyInputs (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    (recordPublic pk history query cached answer).secretKeyInputs =
      if SecretKeyEligible query then query :: history.secretKeyInputs else history.secretKeyInputs := by
  rw [recordPublic, parsed_secretKeyInputs]
  cases parsed : SecurityIndexQuery.parse pk query with
  | none => simp only [decide_eq_true_eq]
  | some pair => rw [if_neg (SecurityIndexQuery.parsed_not_secretKeyEligible pk query pair parsed)]

/-- Add an existing history to a chronological trace. -/
def extend {α : Type} (history : History) (result : Option α × List Query) : Option α × List Query :=
  (result.1, history.secretKeyInputs.reverse ++ result.2)

def project {α : Type} (result : SecurityMonitorGraphView.Result α) : Option α × List Query :=
  (result.value, result.history.secretKeyInputs.reverse)

theorem extend_public {α : Type} (pk : PublicKey) (history : History) (query : Query)
    (cached : Bool) (answer : BitVec 256) (result : Option α × List Query) :
    extend history (result.1, prependPublic (.inr (.inr query)) result.2) =
      extend (recordPublic pk history query cached answer) result := by
  simp only [extend, public_secretKeyInputs, prependPublic]
  split <;> simp [List.reverse_cons, List.append_assoc]

theorem extend_sign {α : Type} (history : History) (message : Message) (cached : Bool) (answer : BitVec 256) :
    extend (α := α) (recordSign history message cached answer) = extend history := rfl

theorem run_bind {σ α β : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (next : α → OracleComp GameWorld β) (cache : σ) :
    (simulateQ implementation (program >>= next)).run' cache =
      ((simulateQ implementation program).run cache >>= fun first =>
        (simulateQ implementation (next first.1)).run' first.2) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

theorem run_map {σ α β : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (f : α → β) (cache : σ) :
    (simulateQ implementation (f <$> program)).run' cache =
      f <$> (simulateQ implementation program).run' cache := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

end SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
