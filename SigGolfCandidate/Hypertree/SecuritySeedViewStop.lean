import SigGolfCandidate.Hypertree.SecuritySeedHonestSign

namespace SigGolfCandidate.Hypertree.SecuritySeedViewStop
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityMonitorView SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The seed monitor sees only public probes. Honest signing, private coins and
all adversary outputs retain their original continuation and responses. -/
noncomputable def seedStopView {α : Type} (seed : Seed) : View α → View (Option α)
  | .done value => .done (some value)
  | .hash input next =>
      if publicSeedHit seed (.inr input) then .done none
      else .hash input (fun answer => seedStopView seed (next answer))
  | .sign pk message next => .sign pk message (fun response => seedStopView seed (next response))
  | .coin n next => .coin n (fun answer => seedStopView seed (next answer))

/-- Exact semantic boundary: the real oracle's seed stop is the same stop in
the shared adversary view, including every internal honest signing query. -/
theorem realize_seedStopView {α : Type} (seed : Seed) (view : View α) :
    stop seed (realize view) = realize (seedStopView seed view) := by
  induction view with
  | done value => rfl
  | hash input next ih =>
    rw [realize, stop_query_bind, seedStopView]
    change (if publicSeedHit seed (.inr input) then pure none else _) = _
    split
    · rfl
    · simp only [realize]
      exact bind_congr ih
  | sign pk message next ih =>
    rw [realize, SecuritySeedHonest.stop_signWire_bind]
    change (_ >>= _) = (_ >>= _)
    exact bind_congr ih
  | coin n next ih =>
    rw [realize, stop_query_bind]
    simp only [isBad, if_false, seedStopView, realize]
    exact bind_congr ih

/-- The full reference experiment admits the same stopped view after its honest
key-generation prefix; no seed hit can occur inside that prefix. -/
theorem stop_program (seed : Seed) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    stop seed (SecurityExperiment.program publicCache adversary rounds) = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      realize (seedStopView seed (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) := by
  rw [SecurityMonitorView.program_eq, (SecuritySeedHonest.keygen.lift seed).stop_bind]
  exact bind_congr (fun _ => realize_seedStopView seed _)

/-- The budget stop and seed stop can be interchanged once either abort is
represented by the same `none`. This retains every completed output exactly. -/
theorem cutoff_stop_join {α : Type} (seed : Seed) (program : OracleComp GameWorld α) (budget : Nat) :
    Option.join <$> stop seed (cutoff program budget) =
      Option.join <$> cutoff (stop seed program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input next ih =>
    rw [cutoff_query_bind]
    by_cases enough : charge input ≤ budget
    · rw [if_pos enough, stop_query_bind, stop_query_bind]
      by_cases hit : isBad seed input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, if_neg hit, cutoff_query_bind, if_pos enough]
        simp only [map_bind]
        exact bind_congr (fun answer => ih answer (budget - charge input))
    · rw [if_neg enough, stop_pure, stop_query_bind]
      by_cases hit : isBad seed input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, cutoff_query_bind, if_neg enough]
        rfl

/-- Fixed-cutoff real-to-independent-private coupling at the shared view boundary.
This is an exact distribution, before any seed or graph probability bound. -/
theorem real_view_stopped {α : Type} (seed : Seed) (view : View α) (budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle seed) (stop seed (cutoff (realize view) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle
        (cutoff (realize (seedStopView seed view)) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation seed _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←realize_seedStopView]
  have same := congrArg (fun program : OracleComp GameWorld (Option α) =>
    (simulateQ idealGameOracle program).run' (∅, ∅)) (cutoff_stop_join seed (realize view) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- The actual experiment has the identical cutoff/seed-stop coupling, with the
shared stopped view reached after the actual honest keygen program. -/
theorem real_program_stopped (seed : Seed) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle seed)
      (stop seed (cutoff (SecurityExperiment.program publicCache adversary rounds) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle (cutoff (do
        let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
        realize (seedStopView seed (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation seed _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←stop_program]
  have same := congrArg (fun program : OracleComp GameWorld (Option SecurityExperiment.Result) =>
    (simulateQ idealGameOracle program).run' (∅, ∅))
    (cutoff_stop_join seed (SecurityExperiment.program publicCache adversary rounds) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- info: 'SigGolfCandidate.Hypertree.SecuritySeedViewStop.real_program_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_program_stopped
end SigGolfCandidate.Hypertree.SecuritySeedViewStop
