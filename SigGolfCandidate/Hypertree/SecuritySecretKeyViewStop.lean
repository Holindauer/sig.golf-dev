import SigGolfCandidate.Hypertree.SecuritySecretKeyHonestSign

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityMonitorView SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The secret key monitor sees only public probes. Honest signing, private coins and
all adversary outputs retain their original continuation and responses. -/
noncomputable def secretKeyStopView {α : Type} (secretKey : SecretKey) : View α → View (Option α)
  | .done value => .done (some value)
  | .hash input next =>
      if publicSecretKeyHit secretKey (.inr input) then .done none
      else .hash input (fun answer => secretKeyStopView secretKey (next answer))
  | .sign pk message next => .sign pk message (fun response => secretKeyStopView secretKey (next response))
  | .coin n next => .coin n (fun answer => secretKeyStopView secretKey (next answer))

/-- Exact semantic boundary: the real oracle's secret key stop is the same stop in
the shared adversary view, including every internal honest signing query. -/
theorem realize_secretKeyStopView {α : Type} (secretKey : SecretKey) (view : View α) :
    stop secretKey (realize view) = realize (secretKeyStopView secretKey view) := by
  induction view with
  | done value => rfl
  | hash input next ih =>
    rw [realize, stop_query_bind, secretKeyStopView]
    change (if publicSecretKeyHit secretKey (.inr input) then pure none else _) = _
    split
    · rfl
    · simp only [realize]
      exact bind_congr ih
  | sign pk message next ih =>
    rw [realize, SecuritySecretKeyHonest.stop_signWire_bind]
    change (_ >>= _) = (_ >>= _)
    exact bind_congr ih
  | coin n next ih =>
    rw [realize, stop_query_bind]
    simp only [isBad, if_false, secretKeyStopView, realize]
    exact bind_congr ih

/-- The full reference experiment admits the same stopped view after its honest
key-generation prefix; no secret key hit can occur inside that prefix. -/
theorem stop_program (secretKey : SecretKey) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    stop secretKey (SecurityExperiment.program publicCache adversary rounds) = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      realize (secretKeyStopView secretKey (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) := by
  rw [SecurityMonitorView.program_eq, (SecuritySecretKeyHonest.keygen.lift secretKey).stop_bind]
  exact bind_congr (fun _ => realize_secretKeyStopView secretKey _)

/-- The budget stop and secret key stop can be interchanged once either abort is
represented by the same `none`. This retains every completed output exactly. -/
theorem cutoff_stop_join {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) (budget : Nat) :
    Option.join <$> stop secretKey (cutoff program budget) =
      Option.join <$> cutoff (stop secretKey program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input next ih =>
    rw [cutoff_query_bind]
    by_cases enough : charge input ≤ budget
    · rw [if_pos enough, stop_query_bind, stop_query_bind]
      by_cases hit : isBad secretKey input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, if_neg hit, cutoff_query_bind, if_pos enough]
        simp only [map_bind]
        exact bind_congr (fun answer => ih answer (budget - charge input))
    · rw [if_neg enough, stop_pure, stop_query_bind]
      by_cases hit : isBad secretKey input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, cutoff_query_bind, if_neg enough]
        rfl

/-- Fixed-cutoff real-to-independent-private coupling at the shared view boundary.
This is an exact distribution, before any secret key or graph probability bound. -/
theorem real_view_stopped {α : Type} (secretKey : SecretKey) (view : View α) (budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle secretKey) (stop secretKey (cutoff (realize view) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle
        (cutoff (realize (secretKeyStopView secretKey view)) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation secretKey _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←realize_secretKeyStopView]
  have same := congrArg (fun program : OracleComp GameWorld (Option α) =>
    (simulateQ idealGameOracle program).run' (∅, ∅)) (cutoff_stop_join secretKey (realize view) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- The actual experiment has the identical cutoff/secret key-stop coupling, with the
shared stopped view reached after the actual honest keygen program. -/
theorem real_program_stopped (secretKey : SecretKey) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle secretKey)
      (stop secretKey (cutoff (SecurityExperiment.program publicCache adversary rounds) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle (cutoff (do
        let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
        realize (secretKeyStopView secretKey (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation secretKey _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←stop_program]
  have same := congrArg (fun program : OracleComp GameWorld (Option SecurityExperiment.Result) =>
    (simulateQ idealGameOracle program).run' (∅, ∅))
    (cutoff_stop_join secretKey (SecurityExperiment.program publicCache adversary rounds) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop.real_program_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_program_stopped
end SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop
