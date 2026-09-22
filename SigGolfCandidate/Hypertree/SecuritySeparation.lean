import SigGolfCandidate.Hypertree.SecurityDerivation

namespace SigGolfCandidate.Hypertree.SecuritySeparation
open SigGolf OracleComp OracleSpec SecurityDerivation SecuritySeed
set_option backward.isDefEq.respectTransparency false

abbrev SplitCache := QueryCache SecretSpec × QueryCache HashSpec

/-- Real private/public calls share precisely one random-oracle cache. -/
noncomputable def realOracle (seed : Seed) :
    QueryImpl SplitWorld (StateT (QueryCache HashSpec) ProbComp)
  | .inl slot => randomOracle (input seed slot)
  | .inr query => randomOracle query

/-- The real two-port handler is exactly the organizer's shared random oracle
applied after expanding private derivations into their concrete H inputs. -/
theorem simulate_realOracle {α : Type} (seed : Seed) (program : OracleComp SplitWorld α) :
    simulateQ (realOracle seed) program =
      simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (simulateQ (realImplementation seed) program) := by
  have step (query : SplitWorld.Domain) :
      simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (realImplementation seed query) = realOracle seed query := by
    cases query <;> simp [realImplementation, realDerivation, realOracle]
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, step, ih]

/-- Ideal private derivations and public H use independent lazy caches. The seed
is absent from this implementation. -/
noncomputable def idealOracle : QueryImpl SplitWorld (StateT SplitCache ProbComp)
  | .inl slot => StateT.mk fun caches => do
      let result ← (randomOracle (spec := SecretSpec) slot).run caches.1
      return (result.1, (result.2, caches.2))
  | .inr query => StateT.mk fun caches => do
      let result ← (randomOracle (spec := HashSpec) query).run caches.2
      return (result.1, (caches.1, result.2))

/-- A seed guess must use an actual private-derivation input shape. In particular,
public chain/hash-node domains do not consume seed-guess budget. -/
def SeedEligible (query : Query) : Prop := ∃ seed slot, input seed slot = query

theorem seedEligible_input (seed : Seed) (slot : Slot) : SeedEligible (input seed slot) :=
  ⟨seed, slot, rfl⟩

/-- Only public calls can guess the seed. Honest private derivation requests are
served through their typed slots and never trigger the monitor. -/
def publicSeedHit (seed : Seed) : SplitWorld.Domain → Prop
  | .inl _ => False
  | .inr query => SeedEligible query ∧ SeedAt query seed

/-- The monitor fires exactly on the real private-input range for this seed. -/
theorem publicSeedHit_iff (seed : Seed) (query : Query) :
    publicSeedHit seed (.inr query) ↔ ∃ slot, input seed slot = query := by
  constructor
  · rintro ⟨⟨other, slot, same⟩, atSeed⟩
    have eqSeed : other = seed := seedAt_unique (same ▸ input_seedAt other slot) atSeed
    subst other
    exact ⟨slot, same⟩
  · rintro ⟨slot, rfl⟩
    exact ⟨seedEligible_input seed slot, input_seedAt seed slot⟩

noncomputable def stopped {α : Type} (seed : Seed) (program : OracleComp SplitWorld α) :
    OracleComp SplitWorld (Option α) := by
  classical
  exact OracleComp.construct (fun value => pure (some value))
    (fun query _ next => if publicSeedHit seed query then pure none else do
      let answer ← liftM (SplitWorld.query query)
      next answer) program

@[simp] theorem stopped_pure {α : Type} (seed : Seed) (value : α) :
    stopped seed (pure value) = pure (some value) := rfl

open scoped Classical in
theorem stopped_query_bind {α : Type} (seed : Seed) (query : SplitWorld.Domain)
    (next : SplitWorld.Range query → OracleComp SplitWorld α) :
    stopped seed (liftM (SplitWorld.query query) >>= next) =
      (if publicSeedHit seed query then pure none else do
        let answer ← liftM (SplitWorld.query query)
        stopped seed (next answer)) := rfl

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl SplitWorld (StateT σ ProbComp)) (query : SplitWorld.Domain)
    (next : SplitWorld.Range query → OracleComp SplitWorld α) (cache : σ) :
    (simulateQ implementation (liftM (SplitWorld.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- The shared real cache contains both the private derivations and all public
answers outside the seed-guess set. No relationship is imposed at already-bad inputs. -/
structure Related (seed : Seed) (real : QueryCache HashSpec) (ideal : SplitCache) : Prop where
  privateInputs : ∀ slot, real (input seed slot) = ideal.1 slot
  publicInputs : ∀ query, ¬publicSeedHit seed (.inr query) → real query = ideal.2 query

theorem Related.privateStep {seed : Seed} {real : QueryCache HashSpec} {ideal : SplitCache}
    (related : Related seed real ideal) (slot : Slot) (answer : BitVec 256) :
    Related seed (real.cacheQuery (input seed slot) answer)
      (ideal.1.cacheQuery slot answer, ideal.2) := by
  constructor
  · intro other
    by_cases same : other = slot
    · subst other; simp
    · have hinput : input seed other ≠ input seed slot := fun h => same (input_injective seed h)
      simp only [QueryCache.cacheQuery_of_ne _ _ hinput, QueryCache.cacheQuery_of_ne _ _ same]
      exact related.privateInputs other
  · intro query good
    have different : query ≠ input seed slot := by
      intro same
      subst query
      exact good ⟨seedEligible_input seed slot, input_seedAt seed slot⟩
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    exact related.publicInputs query good

theorem Related.publicStep {seed : Seed} {real : QueryCache HashSpec} {ideal : SplitCache}
    (related : Related seed real ideal) (query : Query) (answer : BitVec 256)
    (good : ¬publicSeedHit seed (.inr query)) :
    Related seed (real.cacheQuery query answer) (ideal.1, ideal.2.cacheQuery query answer) := by
  constructor
  · intro slot
    have different : input seed slot ≠ query := by
      intro same
      exact good (same ▸ ⟨seedEligible_input seed slot, input_seedAt seed slot⟩)
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    exact related.privateInputs slot
  · intro other goodOther
    by_cases same : other = query
    · subst other; simp
    · simp only [QueryCache.cacheQuery_of_ne _ _ same]
      exact related.publicInputs other goodOther

/-- One coupled query permits arbitrary state-dependent continuations. This is
also the kernel used when inserting the adversary's private-coin queries. -/
theorem couple_query_good {α : Type} (seed : Seed) (query : SplitWorld.Domain)
    (real : QueryCache HashSpec) (ideal : SplitCache) (related : Related seed real ideal)
    (good : ¬publicSeedHit seed query)
    (leftNext : SplitWorld.Range query → QueryCache HashSpec → ProbComp α)
    (rightNext : SplitWorld.Range query → SplitCache → ProbComp α)
    (nextRelated : ∀ answer left right, Related seed left right →
      leftNext answer left = rightNext answer right) :
    ((realOracle seed query).run real >>= fun result => leftNext result.1 result.2) =
      ((idealOracle query).run ideal >>= fun result => rightNext result.1 result.2) := by
  cases query with
  | inl slot =>
    dsimp [SplitWorld, SecretSpec] at leftNext rightNext nextRelated ⊢
    simp only [realOracle, idealOracle, StateT.run, StateT.mk, bind_assoc, pure_bind]
    change ((randomOracle (spec := HashSpec) (input seed slot)).run real >>= fun result =>
      leftNext result.1 result.2) =
      ((randomOracle (spec := SecretSpec) slot).run ideal.1 >>= fun result =>
        rightNext result.1 (result.2, ideal.2))
    have same := related.privateInputs slot
    cases hr : real (input seed slot) with
    | none =>
      have hi : ideal.1 slot = none := same.symm.trans hr
      rw [randomOracle.run_eq, hr, randomOracle.run_eq, hi]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro answer
      exact nextRelated answer _ _ (related.privateStep slot answer)
    | some answer =>
      have hi : ideal.1 slot = some answer := same.symm.trans hr
      rw [randomOracle.run_eq, hr, randomOracle.run_eq, hi]
      simp only [pure_bind]
      exact nextRelated answer real ideal related
  | inr query =>
    dsimp [SplitWorld] at leftNext rightNext nextRelated ⊢
    simp only [realOracle, idealOracle, StateT.run, StateT.mk, bind_assoc, pure_bind]
    change ((randomOracle (spec := HashSpec) query).run real >>= fun result =>
      leftNext result.1 result.2) =
      ((randomOracle (spec := HashSpec) query).run ideal.2 >>= fun result =>
        rightNext result.1 (ideal.1, result.2))
    have same := related.publicInputs query good
    cases hr : real query with
    | none =>
      have hi : ideal.2 query = none := same.symm.trans hr
      rw [randomOracle.run_eq, hr, randomOracle.run_eq, hi]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro answer
      exact nextRelated answer _ _ (related.publicStep query answer good)
    | some answer =>
      have hi : ideal.2 query = some answer := same.symm.trans hr
      rw [randomOracle.run_eq, hr, randomOracle.run_eq, hi]
      simp only [pure_bind]
      exact nextRelated answer real ideal related

/-- Exact adaptive simulation: real seed-derived H calls may be replaced by an
independent private random oracle until a public query guesses the seed. This
uses the actual injective input serialization of both secret chains and nonces. -/
theorem stopped_separation {α : Type} (seed : Seed) (program : OracleComp SplitWorld α)
    (real : QueryCache HashSpec) (ideal : SplitCache) (related : Related seed real ideal) :
    (simulateQ (realOracle seed) (stopped seed program)).run' real =
      (simulateQ idealOracle (stopped seed program)).run' ideal := by
  classical
  induction program using OracleComp.inductionOn generalizing real ideal with
  | pure value => simp
  | query_bind query next ih =>
    rw [stopped_query_bind]
    by_cases hit : publicSeedHit seed query
    · simp [hit]
    · simp only [if_neg hit, run'_query_bind]
      exact couple_query_good seed query real ideal related hit _ _ ih

/-- The real and independent-private worlds start coupled at their empty caches. -/
theorem stopped_separation_empty {α : Type} (seed : Seed) (program : OracleComp SplitWorld α) :
    (simulateQ (realOracle seed) (stopped seed program)).run' ∅ =
      (simulateQ idealOracle (stopped seed program)).run' (∅, ∅) := by
  apply stopped_separation
  constructor <;> intros <;> rfl

end SigGolfCandidate.Hypertree.SecuritySeparation
