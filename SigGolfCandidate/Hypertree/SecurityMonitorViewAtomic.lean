import SigGolfCandidate.Hypertree.SecurityMonitorView
import SigGolfCandidate.Hypertree.SecurityGraphStateRoute

namespace SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop
  SecurityGraph SecurityGraphIdeal SecurityGraphOracle SecurityGraphState
  SecurityMonitorView SecurityAtomicCutoff SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Cache := QueryCache HashSpec

/-- Fix the private table and interpret the remaining public queries by the
explicit graph oracle. This is precisely the original two-stage routing. -/
noncomputable def gameImplementation (privateAnswers : PrivateTable) (labels : Labels) :
    QueryImpl GameWorld (StateT Cache ProbComp) :=
  (implementation privateAnswers labels).compose (privateImplementation privateAnswers)

theorem routing {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp GameWorld α) :
    simulateQ (gameImplementation privateAnswers labels) program =
      simulateQ (implementation privateAnswers labels) (fixPrivate privateAnswers program) := by
  exact QueryImpl.simulateQ_compose _ _ _

/-- A stopped execution has no observable final cache. A completed execution
retains the complete output and residual cache together. -/
def completed {α : Type} (result : Option α × Cache) : Option (α × Cache) :=
  result.1.map (fun value => (value, result.2))

noncomputable def actual {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp GameWorld α) (budget : Nat) (cache : Cache) : ProbComp (Option (α × Cache)) :=
  completed <$> (simulateQ (gameImplementation privateAnswers labels) (cutoff program budget)).run cache

theorem actual_bind_enough {α β : Type} (privateAnswers : PrivateTable) (labels : Labels)
    {program : OracleComp GameWorld α} {cost : Nat} (fixed : FixedCost program cost)
    (next : α → OracleComp GameWorld β) (budget : Nat) (cache : Cache) (enough : cost ≤ budget) :
    actual privateAnswers labels (program >>= next) budget cache =
      ((simulateQ (gameImplementation privateAnswers labels) program).run cache >>= fun first =>
        actual privateAnswers labels (next first.1) (budget - cost) first.2) := by
  unfold actual
  rw [fixed.run_bind_enough _ next cache budget enough, map_bind]

/-- Atomic abort is exact after erasing the final cache only on aborted runs. -/
theorem actual_bind_insufficient {α β : Type} (privateAnswers : PrivateTable) (labels : Labels)
    {program : OracleComp GameWorld α} {cost : Nat} (fixed : FixedCost program cost)
    (next : α → OracleComp GameWorld β) (budget : Nat) (cache : Cache) (short : budget < cost) :
    𝒮[actual privateAnswers labels (program >>= next) budget cache] =
      𝒮[(pure none : ProbComp (Option (β × Cache)))] := by
  let computation := (simulateQ (gameImplementation privateAnswers labels)
    (cutoff (program >>= next) budget)).run cache
  have allNone (result : Option β × Cache) (member : result ∈ support computation) :
      completed result = none := by
    have firstMember : result.1 ∈ support
        ((simulateQ (gameImplementation privateAnswers labels) (cutoff (program >>= next) budget)).run' cache) := by
      rw [StateT.run'_eq, support_map]
      exact ⟨result, member, rfl⟩
    have stopped := fixed.bind_insufficient next budget short result.1
      (support_simulateQ_run'_subset _ _ _ firstMember)
    simp only [completed, stopped, Option.map_none]
  change 𝒮[completed <$> computation] = _
  calc
    _ = 𝒮[(fun _ => (none : Option (β × Cache))) <$> computation] := by
      simp only [map_eq_pure_bind]
      apply evalSPMF_bind_congr
      intro result member
      rw [allNone result member]
    _ = _ := by
      apply evalSPMF_ext
      intro result
      simp only [map_eq_pure_bind, probOutput_bind_const]
      simp

/-- Atomic shared-view execution. Public probes cost one, an entire honest
signature costs 117508, and private coins cost zero. Aborted runs expose no
cache; every normal return carries the exact residual oracle state. -/
noncomputable def execute {α : Type} (privateAnswers : PrivateTable) (labels : Labels) :
    View α → Nat → Cache → ProbComp (Option (α × Cache))
  | .done value, _, cache => pure (some (value, cache))
  | .hash input next, budget, cache =>
      if 1 ≤ budget then do
        let answer ← (publicOracle privateAnswers labels input).run cache
        execute privateAnswers labels (next answer.1) (budget - 1) answer.2
      else pure none
  | .sign pk message next, budget, cache =>
      if 117508 ≤ budget then do
        let answer ← (randomOracle (spec := HashSpec)
          (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))).run cache
        let response := SecurityExperiment.serialize
          (SecurityGraphSigner.signature privateAnswers labels (privateAnswers (.randomizer message))
            (answer.1.extractLsb' 0 160))
        execute privateAnswers labels (next response) (budget - 117508) answer.2
      else pure none
  | .coin n next, budget, cache => do
      let answer ← liftM (unifSpec.query n)
      execute privateAnswers labels (next answer) budget cache

private theorem public_run (privateAnswers : PrivateTable) (labels : Labels) (input : Query) (cache : Cache) :
    (simulateQ (gameImplementation privateAnswers labels)
      (liftM (GameWorld.query (.inr (.inr input))))).run cache =
      (publicOracle privateAnswers labels input).run cache := by
  rw [routing]
  simp only [fixPrivate, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, privateImplementation, implementation, QueryImpl.add_apply_inr]

private theorem coin_run (privateAnswers : PrivateTable) (labels : Labels) (n : Nat) (cache : Cache) :
    (simulateQ (gameImplementation privateAnswers labels)
      (liftM (GameWorld.query (.inl n)))).run cache =
      (fun answer => (answer, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  rw [routing]
  rfl

/-- Exact graph-reference to shared-view bridge, for every adaptive view and
budget. It preserves the full final result/cache joint distribution. -/
theorem realize_execute {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (view : View α) (budget : Nat) (cache : Cache) :
    𝒮[actual privateAnswers labels (realize view) budget cache] =
      𝒮[execute privateAnswers labels view budget cache] := by
  induction view generalizing budget cache with
  | done value => simp [realize, actual, completed, execute]
  | hash input next ih =>
    have fixed : FixedCost (liftM (GameWorld.query (.inr (.inr input)))) 1 := by
      simpa only [bind_pure, charge, Nat.add_zero] using
        FixedCost.query (.inr (.inr input)) Pure.pure 0 (fun answer => FixedCost.pure answer)
    change 𝒮[actual privateAnswers labels
      (liftM (GameWorld.query (.inr (.inr input))) >>= fun answer => realize (next answer)) budget cache] = _
    unfold execute
    split
    next enough =>
      rw [actual_bind_enough _ _ fixed _ _ _ enough, public_run]
      apply evalSPMF_bind_congr
      intro result _
      exact ih result.1 _ _
    next short => exact actual_bind_insufficient _ _ fixed _ _ _ (by omega)
  | sign pk message next ih =>
    change 𝒮[actual privateAnswers labels
      ((SecurityExperiment.signWire pk message).liftComp GameWorld >>= fun answer => realize (next answer)) budget cache] = _
    unfold execute
    split
    next enough =>
      rw [actual_bind_enough _ _ (SecurityAtomicCounts.signWire pk message) _ _ _ enough,
        routing, routed_signWire_run, bind_map_left]
      apply evalSPMF_bind_congr
      intro result _
      exact ih _ _ _
    next short => exact actual_bind_insufficient _ _ (SecurityAtomicCounts.signWire pk message) _ _ _ (by omega)
  | coin n next ih =>
    have fixed : FixedCost (liftM (GameWorld.query (.inl n))) 0 := by
      simpa only [bind_pure, charge, Nat.add_zero] using
        FixedCost.query (.inl n) Pure.pure 0 (fun answer => FixedCost.pure answer)
    change 𝒮[actual privateAnswers labels
      (liftM (GameWorld.query (.inl n)) >>= fun answer => realize (next answer)) budget cache] = _
    rw [actual_bind_enough _ _ fixed _ _ _ (Nat.zero_le _), coin_run, bind_map_left]
    simp only [Nat.sub_zero, execute]
    apply evalSPMF_bind_congr
    intro answer _
    exact ih answer _ _

/-- The actual finite reference interaction uses the same atomic interpreter. -/
theorem interact_execute (privateAnswers : PrivateTable) (labels : Labels)
    (adversary : Adversary submission.sizes) (pk : PublicKey) (rounds : Nat)
    (state : adversary.State) (transcript : Transcript submission.sizes) (budget : Nat) (cache : Cache) :
    𝒮[actual privateAnswers labels (SecurityExperiment.interact adversary pk rounds state transcript) budget cache] =
      𝒮[execute privateAnswers labels (ofInteract adversary pk rounds state transcript) budget cache] := by
  rw [← realize_ofInteract]
  exact realize_execute _ _ _ _ _

/-- The full actual reference program performs its fixed-cost key generation,
then enters the shared view with exactly the remaining budget and unchanged
residual cache. This also covers a budget too small to complete key generation. -/
theorem program_execute (privateAnswers : PrivateTable) (labels : Labels)
    (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : Cache) :
    𝒮[actual privateAnswers labels (SecurityExperiment.program publicCache adversary rounds) budget cache] =
      if 739 ≤ budget then
        𝒮[execute privateAnswers labels
          (ofInteract adversary (truncate (labels (.node 159 0))) rounds
            (adversary.initial (truncate (labels (.node 159 0))) publicCache) {}) (budget - 739) cache]
      else 𝒮[(pure none : ProbComp (Option (SecurityExperiment.Result × Cache)))] := by
  rw [SecurityMonitorView.program_eq]
  split
  next enough =>
    rw [actual_bind_enough _ _ SecurityAtomicCounts.keygen _ _ _ enough,
      routing, routed_keygen_run, pure_bind]
    exact realize_execute _ _ _ _ _
  next short => exact actual_bind_insufficient _ _ SecurityAtomicCounts.keygen _ _ _ (by omega)

/-- Forgetting the successful final cache recovers precisely the observable
cutoff experiment under private fixing and the explicit graph oracle. -/
theorem actual_output {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp GameWorld α) (budget : Nat) (cache : Cache) :
    Option.map Prod.fst <$> actual privateAnswers labels program budget cache =
      (simulateQ (implementation privateAnswers labels)
        (fixPrivate privateAnswers (cutoff program budget))).run' cache := by
  rw [actual, Functor.map_map, routing, StateT.run'_eq]
  congr 1
  funext result
  rcases result with ⟨value, cache⟩
  cases value <;> rfl

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic.program_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_execute

end SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic
