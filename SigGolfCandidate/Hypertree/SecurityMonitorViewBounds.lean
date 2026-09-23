import SigGolfCandidate.Hypertree.SecurityMonitorView

namespace SigGolfCandidate.Hypertree.SecurityMonitorView
open SigGolf OracleComp OracleSpec Reference SecurityExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- All honest signing operations use the single experiment public key. -/
def WellFormed {α : Type} (pk : PublicKey) : View α → Prop
  | .done _ => True
  | .hash _ next => ∀ answer, WellFormed pk (next answer)
  | .coin _ next => ∀ answer, WellFormed pk (next answer)
  | .sign signPk _ next => signPk = pk ∧ ∀ answer, WellFormed pk (next answer)

/-- A pathwise lifetime bound on actual honest signing actions. -/
def WithinSigns {α : Type} : Nat → View α → Prop
  | _, .done _ => True
  | remaining, .hash _ next => ∀ answer, WithinSigns remaining (next answer)
  | remaining, .coin _ next => ∀ answer, WithinSigns remaining (next answer)
  | remaining, .sign _ _ next => 0 < remaining ∧ ∀ answer, WithinSigns (remaining - 1) (next answer)

theorem ofHash_wellFormed {α β : Type} (pk : PublicKey) (program : OracleComp HashSpec α)
    (next : α → View β) (well : ∀ value, WellFormed pk (next value)) : WellFormed pk (ofHash program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact well value
  | query_bind query resume ih => exact ih

theorem ofHash_withinSigns {α β : Type} (remaining : Nat) (program : OracleComp HashSpec α)
    (next : α → View β) (within : ∀ value, WithinSigns remaining (next value)) :
    WithinSigns remaining (ofHash program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact within value
  | query_bind query resume ih => exact ih

theorem ofCheck_wellFormed (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) : WellFormed pk (ofCheck pk transcript forgery) := by
  cases forgery <;> apply ofHash_wellFormed <;> exact fun _ => True.intro

theorem ofCheck_withinSigns (remaining : Nat) (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) : WithinSigns remaining (ofCheck pk transcript forgery) := by
  cases forgery <;> apply ofHash_withinSigns <;> exact fun _ => True.intro

/-- The concrete view preserves the single-key organizer interface. -/
theorem ofInteract_wellFormed (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) :
    WellFormed pk (ofInteract adversary pk rounds state transcript) := by
  induction rounds generalizing state transcript with
  | zero => exact True.intro
  | succ rounds ih =>
    unfold ofInteract
    cases action : adversary.step state with
    | submit forgery => exact ofCheck_wellFormed pk transcript forgery
    | hash input resume => exact fun answer => ih (resume answer) transcript
    | sample n resume => exact fun answer => ih (resume answer) transcript
    | step next => exact ih next transcript
    | sign request resume =>
      dsimp only
      split
      · exact ⟨rfl, fun result => ih (resume result) _⟩
      · exact True.intro

/-- The real lifetime gate bounds all future signing operations, independent of
the adversary's hash queries, private samples, and signing-cache contents. -/
theorem ofInteract_withinSigns (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) :
    WithinSigns (LIFETIME - transcript.signingRequests) (ofInteract adversary pk rounds state transcript) := by
  induction rounds generalizing state transcript with
  | zero => exact True.intro
  | succ rounds ih =>
    unfold ofInteract
    cases action : adversary.step state with
    | submit forgery => exact ofCheck_withinSigns _ pk transcript forgery
    | hash input resume => exact fun answer => ih (resume answer) transcript
    | sample n resume => exact fun answer => ih (resume answer) transcript
    | step next => exact ih next transcript
    | sign request resume =>
      dsimp only
      split
      next allowed =>
        refine ⟨by omega, fun result => ?_⟩
        have later := ih (resume result) (SecurityExperimentAtomic.afterSign transcript request.message result)
        change WithinSigns ((LIFETIME - transcript.signingRequests) - 1)
          (ofInteract adversary pk rounds (resume result)
            (SecurityExperimentAtomic.afterSign transcript request.message result))
        rw [Nat.sub_sub]
        exact later
      next denied => exact True.intro

end SigGolfCandidate.Hypertree.SecurityMonitorView
