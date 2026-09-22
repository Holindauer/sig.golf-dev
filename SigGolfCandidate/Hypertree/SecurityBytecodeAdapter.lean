import SigGolfCandidate.Hypertree.SecurityBytecodeExperiment

namespace SigGolfCandidate.Hypertree.SecurityBytecodeAdapter
open SigGolf OracleComp OracleSpec SecurityDerivation SecurityGameHop SecurityBytecode
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- Resolve the private derivation port while retaining the attacker's private coins. -/
def translate (seed : Seed) : QueryImpl GameWorld (OracleComp World) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := OracleComp World) +
    fun query => (realImplementation seed query).liftComp World

abbrev resolve {α : Type} (seed : Seed) (program : OracleComp GameWorld α) : OracleComp World α :=
  simulateQ (translate seed) program

theorem resolve_split {α : Type} (seed : Seed) (program : OracleComp SplitWorld α) :
    resolve seed (program.liftComp GameWorld) =
      (simulateQ (realImplementation seed) program).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    cases query <;>
      simp [resolve, translate, realImplementation, realDerivation] at ih ⊢ <;>
      exact bind_congr ih

theorem resolve_hash {α : Type} (seed : Seed) (program : OracleComp HashSpec α) :
    resolve seed (program.liftComp GameWorld) = program.liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [resolve] at ih ⊢
    simp [OracleComp.liftComp_bind, OracleComp.liftComp_query, translate,
      realImplementation, simulateQ_bind] at ih ⊢
    exact bind_congr ih

theorem counted_bind {α β : Type} (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld β) :
    SecurityBudget.counted (program >>= next) = (do
      let first ← SecurityBudget.counted program
      let second ← SecurityBudget.counted (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query tail ih =>
    simp only [bind_assoc, SecurityBudget.counted_query_bind, ih, pure_bind]
    apply bind_congr
    intro answer
    apply bind_congr
    intro first
    apply bind_congr
    intro second
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem counted_map {α β : Type} (f : α → β) (program : OracleComp GameWorld α) :
    SecurityBudget.counted (f <$> program) =
      (fun result => (f result.1,result.2)) <$> SecurityBudget.counted program := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, counted_bind, SecurityBudget.counted_pure, pure_bind, Nat.add_zero]

theorem resolve_counted_split {α : Type} (seed : Seed) (program : OracleComp SplitWorld α) :
    resolve seed (SecurityBudget.counted (program.liftComp GameWorld)) =
      (countHash (simulateQ (realImplementation seed) program)).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    change resolve seed (SecurityBudget.counted (liftM (GameWorld.query (.inr query)) >>= _)) = _
    rw [SecurityBudget.counted_query_bind]
    cases query <;>
      simp [resolve, translate, realImplementation, realDerivation, SecurityBudget.charge,
        countHash_query_bind] at ih ⊢ <;>
      exact bind_congr (fun answer => by rw [ih])

theorem resolve_counted_hash {α : Type} (seed : Seed) (program : OracleComp HashSpec α) :
    resolve seed (SecurityBudget.counted (program.liftComp GameWorld)) =
      (countHash program).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    change resolve seed (SecurityBudget.counted (liftM (GameWorld.query (.inr (.inr query))) >>= _)) = _
    rw [SecurityBudget.counted_query_bind]
    simp [resolve, translate, realImplementation, SecurityBudget.charge,
      countHash_query_bind] at ih ⊢
    exact bind_congr (fun answer => by rw [ih])

/-- Add the already charged prefix to the reference experiment's local count. -/
def project (initial : Nat) (result : SecurityExperiment.Result × Nat) : AttackResult :=
  ⟨result.1.won, initial + result.2⟩

theorem project_query (seed : Seed) (initial : Nat) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld SecurityExperiment.Result) :
    project initial <$> resolve seed (SecurityBudget.counted (liftM (GameWorld.query query) >>= next)) =
      (translate seed query >>= fun answer =>
        project (initial + SecurityBudget.charge query) <$> resolve seed (SecurityBudget.counted (next answer))) := by
  simp only [SecurityBudget.counted_query_bind, resolve, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, map_bind, map_pure]
  simp only [map_eq_bind_pure_comp, Function.comp_def, project, Nat.add_comm, Nat.add_left_comm]

theorem project_bind {α : Type} (seed : Seed) (initial : Nat) (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld SecurityExperiment.Result) :
    project initial <$> resolve seed (SecurityBudget.counted (program >>= next)) =
      (resolve seed (SecurityBudget.counted program) >>= fun result =>
        project (initial + result.2) <$> resolve seed (SecurityBudget.counted (next result.1))) := by
  simp only [counted_bind, resolve, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  simp only [map_eq_bind_pure_comp, Function.comp_def, project, Nat.add_assoc]

theorem check (seed : Seed) (pk : PublicKey) (transcript : Transcript submission.sizes)
    (initial : Nat) (candidate : Forgery submission.sizes) :
    project initial <$> resolve seed (SecurityBudget.counted (SecurityExperiment.check pk transcript candidate)) =
      (referenceCheck pk {transcript with hashCalls := initial} candidate).liftComp World := by
  cases candidate <;>
    simp only [SecurityExperiment.check, counted_bind, SecurityBudget.counted_pure, pure_bind, Nat.add_zero,
      resolve, simulateQ_bind, simulateQ_pure, map_bind, map_pure, referenceCheck,
      OracleComp.liftComp_bind, OracleComp.liftComp_pure]
  all_goals
    rw [show simulateQ (translate seed) (SecurityBudget.counted ((SecurityVerify.verifyCompact _ _ _).liftComp GameWorld)) =
      (countHash (SecurityVerify.verifyCompact _ _ _)).liftComp World from resolve_counted_hash seed _]
    rfl

theorem interaction (adversary : Adversary submission.sizes) (seed : Seed) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) (initial : Nat) :
    project initial <$> resolve seed (SecurityBudget.counted (SecurityExperiment.interact adversary pk rounds state transcript)) =
      interactWith referenceInterface adversary seed pk rounds state {transcript with hashCalls := initial} := by
  induction rounds generalizing state transcript initial with
  | zero => simp [SecurityExperiment.interact, interactWith, project]
  | succ rounds ih =>
    simp only [SecurityExperiment.interact, interactWith]
    cases action : adversary.step state <;> simp only
    case submit candidate => exact check seed pk transcript initial candidate
    case hash input resume =>
      rw [project_query]
      change ((liftM (HashSpec.query input) : OracleComp World _) >>= _) = _
      exact bind_congr (fun answer => ih (resume answer) transcript (initial+1))
    case sign request resume =>
      split
      · rw [project_bind, resolve_counted_split, SecurityExperiment.simulate_signWire]
        apply bind_congr
        intro result
        rw [ih]
        rfl
      · simp [project]
    case sample n resume =>
      rw [project_query]
      exact bind_congr (fun answer => ih (resume answer) transcript initial)
    case step next => exact ih next transcript initial

theorem seeded_program (adversary : Adversary submission.sizes) (rounds : Nat) (seed : Seed) :
    project 0 <$> resolve seed (SecurityBudget.counted (SecurityExperiment.program KeygenFunctional.zeroCache adversary rounds)) =
      seededWith referenceInterface adversary rounds seed := by
  unfold SecurityExperiment.program
  rw [project_bind, resolve_counted_split, SecurityIdealKeygen.simulate_keygen]
  simp only [seededWith, referenceInterface, referenceKeygen, OracleComp.liftComp_bind,
    OracleComp.liftComp_pure, bind_assoc, pure_bind, Nat.zero_add]
  apply bind_congr
  intro result
  exact interaction adversary seed result.1 rounds (adversary.initial result.1 KeygenFunctional.zeroCache) {} result.2

theorem simulate_real {α : Type} (seed : Seed) (program : OracleComp GameWorld α) :
    simulateQ (realGameOracle seed) program = simulateQ SecurityCache.implementation (resolve seed program) := by
  have hash_query (query : Query) :
      simulateQ SecurityCache.implementation ((liftM (HashSpec.query query) : OracleComp HashSpec _).liftComp World) =
        (randomOracle (spec := HashSpec) query : StateT (QueryCache HashSpec) ProbComp _) := by
    rw [OracleComp.liftComp_query]
    change simulateQ SecurityCache.implementation (liftM (World.query (.inr query))) = _
    rw [simulateQ_spec_query]
    rfl
  have step (query : GameWorld.Domain) :
      simulateQ SecurityCache.implementation (translate seed query) = realGameOracle seed query := by
    cases query with
    | inl coin => rfl
    | inr query =>
      cases query with
      | inl slot => exact hash_query (input seed slot)
      | inr query => exact hash_query query
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [resolve, simulateQ_bind, simulateQ_spec_query, step] at ih ⊢
    exact bind_congr ih

/-- The organizer-shaped reference interface is exactly the counted, seeded reduction game. -/
theorem reference_experiment (adversary : Adversary submission.sizes) (rounds : Nat) :
    SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds =
      experimentWith referenceInterface adversary rounds := by
  rw [experiment_seeded]
  unfold SecurityExperiment.realExperiment
  apply bind_congr
  intro seed
  rw [simulate_real]
  calc
    _ = SecurityGraphHidden.observe
      (project 0 <$> resolve seed (SecurityBudget.counted (SecurityExperiment.program KeygenFunctional.zeroCache adversary rounds))) ∅ := by
        simp only [SecurityGraphHidden.observe, simulateQ_map, StateT.run'_eq,
          StateT.run_map, Functor.map_map, project, Nat.zero_add]
    _ = _ := congrArg (fun program => SecurityGraphHidden.observe program ∅) (seeded_program adversary rounds seed)

/-- Exact security-game distribution for the actual four-program submission. -/
theorem experiment_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
      𝒮[SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds] := by
  rw [reference_experiment]
  exact SecurityBytecode.experiment_equivalent adversary rounds

theorem probability_eq (adversary : Adversary submission.sizes) (rounds : Nat) (event : AttackResult → Prop) :
    Pr[event | submission.securityExperiment adversary rounds] =
      Pr[event | SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds] := by
  simp only [probEvent_def, experiment_equivalent]

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecodeAdapter.experiment_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_equivalent

end SigGolfCandidate.Hypertree.SecurityBytecodeAdapter
