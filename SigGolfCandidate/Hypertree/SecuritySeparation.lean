import SigGolfCandidate.Hypertree.SecurityDerivation

namespace SigGolfCandidate.Hypertree.SecuritySeparation
open SigGolf OracleComp OracleSpec SecurityDerivation SecuritySecretKey
set_option backward.isDefEq.respectTransparency false

abbrev SplitCache := QueryCache SecretSpec × QueryCache HashSpec

/-- Real private/public calls share precisely one random-oracle cache. -/
noncomputable def realOracle (secretKey : SecretKey) :
    QueryImpl SplitWorld (StateT (QueryCache HashSpec) ProbComp)
  | .inl slot => randomOracle (input secretKey slot)
  | .inr query => randomOracle query

/-- The real two-port handler is exactly the organizer's shared random oracle
applied after expanding private derivations into their concrete H inputs. -/
theorem simulate_realOracle {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α) :
    simulateQ (realOracle secretKey) program =
      simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (simulateQ (realImplementation secretKey) program) := by
  have step (query : SplitWorld.Domain) :
      simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (realImplementation secretKey query) = realOracle secretKey query := by
    cases query <;> simp [realImplementation, realDerivation, realOracle]
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, step, ih]

/-- Ideal private derivations and public H use independent lazy caches. The secret key
is absent from this implementation. -/
noncomputable def idealOracle : QueryImpl SplitWorld (StateT SplitCache ProbComp)
  | .inl slot => StateT.mk fun caches => do
      let result ← (randomOracle (spec := SecretSpec) slot).run caches.1
      return (result.1, (result.2, caches.2))
  | .inr query => StateT.mk fun caches => do
      let result ← (randomOracle (spec := HashSpec) query).run caches.2
      return (result.1, (caches.1, result.2))

/-- A secret key guess must use an actual private-derivation input shape. In particular,
public chain/hash-node domains do not consume secret key-guess budget. -/
def SecretKeyEligible (query : Query) : Prop := ∃ secretKey slot, input secretKey slot = query

theorem secretKeyEligible_input (secretKey : SecretKey) (slot : Slot) : SecretKeyEligible (input secretKey slot) :=
  ⟨secretKey, slot, rfl⟩

/-- Only public calls can guess the secret key. Honest private derivation requests are
served through their typed slots and never trigger the monitor. -/
def publicSecretKeyHit (secretKey : SecretKey) : SplitWorld.Domain → Prop
  | .inl _ => False
  | .inr query => SecretKeyEligible query ∧ SecretKeyAt query secretKey

/-- The monitor fires exactly on the real private-input range for this secret key. -/
theorem publicSecretKeyHit_iff (secretKey : SecretKey) (query : Query) :
    publicSecretKeyHit secretKey (.inr query) ↔ ∃ slot, input secretKey slot = query := by
  constructor
  · rintro ⟨⟨other, slot, same⟩, atSecretKey⟩
    have eqSecretKey : other = secretKey := secretKeyAt_unique (same ▸ input_secretKeyAt other slot) atSecretKey
    subst other
    exact ⟨slot, same⟩
  · rintro ⟨slot, rfl⟩
    exact ⟨secretKeyEligible_input secretKey slot, input_secretKeyAt secretKey slot⟩

noncomputable def stopped {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α) :
    OracleComp SplitWorld (Option α) := by
  classical
  exact OracleComp.construct (fun value => pure (some value))
    (fun query _ next => if publicSecretKeyHit secretKey query then pure none else do
      let answer ← liftM (SplitWorld.query query)
      next answer) program

@[simp] theorem stopped_pure {α : Type} (secretKey : SecretKey) (value : α) :
    stopped secretKey (pure value) = pure (some value) := rfl

open scoped Classical in
theorem stopped_query_bind {α : Type} (secretKey : SecretKey) (query : SplitWorld.Domain)
    (next : SplitWorld.Range query → OracleComp SplitWorld α) :
    stopped secretKey (liftM (SplitWorld.query query) >>= next) =
      (if publicSecretKeyHit secretKey query then pure none else do
        let answer ← liftM (SplitWorld.query query)
        stopped secretKey (next answer)) := rfl

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl SplitWorld (StateT σ ProbComp)) (query : SplitWorld.Domain)
    (next : SplitWorld.Range query → OracleComp SplitWorld α) (cache : σ) :
    (simulateQ implementation (liftM (SplitWorld.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- The shared real cache contains both the private derivations and all public
answers outside the secret key-guess set. No relationship is imposed at already-bad inputs. -/
structure Related (secretKey : SecretKey) (real : QueryCache HashSpec) (ideal : SplitCache) : Prop where
  privateInputs : ∀ slot, real (input secretKey slot) = ideal.1 slot
  publicInputs : ∀ query, ¬publicSecretKeyHit secretKey (.inr query) → real query = ideal.2 query

theorem Related.privateStep {secretKey : SecretKey} {real : QueryCache HashSpec} {ideal : SplitCache}
    (related : Related secretKey real ideal) (slot : Slot) (answer : BitVec 256) :
    Related secretKey (real.cacheQuery (input secretKey slot) answer)
      (ideal.1.cacheQuery slot answer, ideal.2) := by
  constructor
  · intro other
    by_cases same : other = slot
    · subst other; simp
    · have hinput : input secretKey other ≠ input secretKey slot := fun h => same (input_injective secretKey h)
      simp only [QueryCache.cacheQuery_of_ne _ _ hinput, QueryCache.cacheQuery_of_ne _ _ same]
      exact related.privateInputs other
  · intro query good
    have different : query ≠ input secretKey slot := by
      intro same
      subst query
      exact good ⟨secretKeyEligible_input secretKey slot, input_secretKeyAt secretKey slot⟩
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    exact related.publicInputs query good

theorem Related.publicStep {secretKey : SecretKey} {real : QueryCache HashSpec} {ideal : SplitCache}
    (related : Related secretKey real ideal) (query : Query) (answer : BitVec 256)
    (good : ¬publicSecretKeyHit secretKey (.inr query)) :
    Related secretKey (real.cacheQuery query answer) (ideal.1, ideal.2.cacheQuery query answer) := by
  constructor
  · intro slot
    have different : input secretKey slot ≠ query := by
      intro same
      exact good (same ▸ ⟨secretKeyEligible_input secretKey slot, input_secretKeyAt secretKey slot⟩)
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    exact related.privateInputs slot
  · intro other goodOther
    by_cases same : other = query
    · subst other; simp
    · simp only [QueryCache.cacheQuery_of_ne _ _ same]
      exact related.publicInputs other goodOther

/-- One coupled query permits arbitrary state-dependent continuations. This is
also the kernel used when inserting the adversary's private-coin queries. -/
theorem couple_query_good {α : Type} (secretKey : SecretKey) (query : SplitWorld.Domain)
    (real : QueryCache HashSpec) (ideal : SplitCache) (related : Related secretKey real ideal)
    (good : ¬publicSecretKeyHit secretKey query)
    (leftNext : SplitWorld.Range query → QueryCache HashSpec → ProbComp α)
    (rightNext : SplitWorld.Range query → SplitCache → ProbComp α)
    (nextRelated : ∀ answer left right, Related secretKey left right →
      leftNext answer left = rightNext answer right) :
    ((realOracle secretKey query).run real >>= fun result => leftNext result.1 result.2) =
      ((idealOracle query).run ideal >>= fun result => rightNext result.1 result.2) := by
  cases query with
  | inl slot =>
    dsimp [SplitWorld, SecretSpec] at leftNext rightNext nextRelated ⊢
    simp only [realOracle, idealOracle, StateT.run, StateT.mk, bind_assoc, pure_bind]
    change ((randomOracle (spec := HashSpec) (input secretKey slot)).run real >>= fun result =>
      leftNext result.1 result.2) =
      ((randomOracle (spec := SecretSpec) slot).run ideal.1 >>= fun result =>
        rightNext result.1 (result.2, ideal.2))
    have same := related.privateInputs slot
    cases hr : real (input secretKey slot) with
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

/-- Exact adaptive simulation: real secret key-derived H calls may be replaced by an
independent private random oracle until a public query guesses the secret key. This
uses the actual injective input serialization of both secret chains and nonces. -/
theorem stopped_separation {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α)
    (real : QueryCache HashSpec) (ideal : SplitCache) (related : Related secretKey real ideal) :
    (simulateQ (realOracle secretKey) (stopped secretKey program)).run' real =
      (simulateQ idealOracle (stopped secretKey program)).run' ideal := by
  classical
  induction program using OracleComp.inductionOn generalizing real ideal with
  | pure value => simp
  | query_bind query next ih =>
    rw [stopped_query_bind]
    by_cases hit : publicSecretKeyHit secretKey query
    · simp [hit]
    · simp only [if_neg hit, run'_query_bind]
      exact couple_query_good secretKey query real ideal related hit _ _ ih

/-- The real and independent-private worlds start coupled at their empty caches. -/
theorem stopped_separation_empty {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α) :
    (simulateQ (realOracle secretKey) (stopped secretKey program)).run' ∅ =
      (simulateQ idealOracle (stopped secretKey program)).run' (∅, ∅) := by
  apply stopped_separation
  constructor <;> intros <;> rfl

end SigGolfCandidate.Hypertree.SecuritySeparation
