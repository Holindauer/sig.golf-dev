import SigGolfCandidate.Hypertree.Reference
import SigGolfCandidate.Hypertree.SecurityUniform
import SigGolfCandidate.Hypertree.SecurityPacking

namespace SigGolfCandidate.Hypertree.SecurityRandomOracle
open SigGolf OracleComp OracleSpec Reference
set_option maxRecDepth 4096

/-- The exact serialized input of the reference hash wrapper. -/
def addressedInput (tag level tree leaf chain step : Nat) (payload : List Byte) : Query :=
  let header : BitVec 64 := BitVec.ofNat 64
    (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32)
  packed (bytes (n := 8) header ++ bytes (n := 24) (BitVec.ofNat 192 tree) ++ payload)

theorem query_eq (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) :
    Reference.query hash tag level tree leaf chain step payload =
      hash (addressedInput tag level tree leaf chain step payload) := rfl

def randomizerInput (secretKey : SecretKey) (message : Message) : Query :=
  addressedInput 6 0 0 0 0 0 (bytes secretKey ++ bytes message)

def indexInput (pk : PublicKey) (message : Message) (r : Bytes 32) : Query :=
  addressedInput 5 0 0 0 0 0 (bytes pk ++ bytes message ++ bytes r)

@[simp] theorem addressedInput_length (tag level tree leaf chain step : Nat)
    (payload : List Byte) :
    (addressedInput tag level tree leaf chain step payload).1 = 8 * (32 + payload.length) := by
  simp [addressedInput, packed, bytes, Nat.add_assoc]
  omega

@[simp] theorem randomizerInput_length (secretKey : SecretKey) (message : Message) :
    (randomizerInput secretKey message).1 = 640 := by simp [randomizerInput, bytes]

@[simp] theorem indexInput_length (pk : PublicKey) (message : Message) (r : Bytes 32) :
    (indexInput pk message r).1 = 896 := by simp [indexInput, bytes]

/-- Separation holds for the actual bit-string oracle inputs, including their lengths. -/
theorem indexInput_ne_randomizerInput (pk : PublicKey) (message other : Message)
    (r : Bytes 32) (secretKey : SecretKey) :
    indexInput pk message r ≠ randomizerInput secretKey other := by
  intro h
  have := congrArg Sigma.fst h
  simp at this

/-- At fixed public key and message, one index input names exactly one randomizer. -/
theorem indexInput_randomizer_injective (pk : PublicKey) (message : Message) :
    Function.Injective (indexInput pk message) := by
  intro first second h
  have hp := SecurityPacking.packed_injective h
  have hb : bytes first = bytes second := by
    simpa [indexInput, addressedInput, List.append_assoc] using hp
  exact SecurityPacking.bytes_injective 32 hb

/-- At a fixed message, a query to the secret-randomizer domain guesses at most one secret key. -/
theorem randomizerInput_secretKey_injective (message : Message) :
    Function.Injective (fun secretKey => randomizerInput secretKey message) := by
  intro first second h
  have hp := SecurityPacking.packed_injective h
  have hb : bytes first = bytes second := by
    simpa [randomizerInput, addressedInput, List.append_assoc] using hp
  exact SecurityPacking.bytes_injective 16 hb

/-- Oracle computation for the exact randomized-index prefix of reference signing. -/
def randomizedIndex (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    OracleComp HashSpec (Bytes 32 × BitVec 160) := do
  let r ← HashSpec.query (randomizerInput secretKey message)
  let answer ← HashSpec.query (indexInput pk message r)
  return (r, answer.extractLsb' 0 160)

theorem eval_randomizedIndex (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    evalWithAnswerFn hash (randomizedIndex secretKey pk message) =
      (Reference.randomizer hash secretKey message,
        Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)) := rfl

/-- Exact lazy-sampling law when the secret randomizer input has not yet been queried.
The index lookup remains a cache lookup: this theorem does not silently assume it fresh. -/
theorem run_randomizedIndex_fresh_randomizer (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (fresh : cache (randomizerInput secretKey message) = none) :
    (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (randomizedIndex secretKey pk message)).run cache = do
        let r ← $ᵗ BitVec 256
        let result ← (randomOracle (spec := HashSpec) (indexInput pk message r)).run
          (cache.cacheQuery (randomizerInput secretKey message) r)
        return ((r, result.1.extractLsb' 0 160), result.2) := by
  simp only [randomizedIndex, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run_bind, StateT.run_pure]
  rw [randomOracle.run_eq, fresh]
  simp

/-- A fresh randomizer query cannot itself populate the index query's cache entry. -/
theorem index_cache_after_randomizer (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (r : Bytes 32) :
    cache.cacheQuery (randomizerInput secretKey message) r (indexInput pk message r) =
      cache (indexInput pk message r) :=
  QueryCache.cacheQuery_of_ne cache r (indexInput_ne_randomizerInput pk message message r secretKey)

/-- Full state-preserving simulation when both inputs are fresh. The two answers are
independent uniforms and both exact input/answer pairs are retained in the shared cache. -/
theorem run_randomizedIndex_fresh (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (fresh : cache (randomizerInput secretKey message) = none)
    (indexFresh : ∀ r, cache (indexInput pk message r) = none) :
    (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (randomizedIndex secretKey pk message)).run cache = do
        let r ← $ᵗ BitVec 256
        let answer ← $ᵗ BitVec 256
        return ((r, answer.extractLsb' 0 160),
          (cache.cacheQuery (randomizerInput secretKey message) r).cacheQuery
            (indexInput pk message r) answer) := by
  rw [run_randomizedIndex_fresh_randomizer secretKey pk message cache fresh]
  apply bind_congr
  intro r
  rw [randomOracle.run_eq, index_cache_after_randomizer, indexFresh]
  simp

/-- The value marginal of the exact prefix under the two freshness conditions. -/
theorem run'_randomizedIndex_fresh (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (fresh : cache (randomizerInput secretKey message) = none)
    (indexFresh : ∀ r, cache (indexInput pk message r) = none) :
    (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (randomizedIndex secretKey pk message)).run' cache = do
        let r ← $ᵗ BitVec 256
        let answer ← $ᵗ BitVec 256
        return (r, answer.extractLsb' 0 160) := by
  rw [StateT.run'_eq, run_randomizedIndex_fresh secretKey pk message cache fresh indexFresh]
  simp [map_bind]

/-- Exactly those nonce values for which the attacker has already populated the
message's index input. This finite set is measured symbolically, not enumerated. -/
def prequeriedRandomizers (cache : QueryCache HashSpec) (pk : PublicKey) (message : Message) :
    Finset (Bytes 32) :=
  Finset.univ.filter fun r => (cache (indexInput pk message r)).isSome

/-- Concrete local reduction for the actual randomized-index computation. With a
fresh secret-randomizer input, its index hits prior targets only by guessing one
of the prequeried nonces or by a fresh 160-bit target hit. The starting cache is
arbitrary and the result retains the cache state. -/
theorem prob_index_mem_le (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (fresh : cache (randomizerInput secretKey message) = none)
    (targets : Finset (BitVec 160)) :
    Pr[fun result => result.1.2 ∈ targets |
      (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (randomizedIndex secretKey pk message)).run cache] ≤
      ((prequeriedRandomizers cache pk message).card : ENNReal) / 2 ^ 256 +
        (targets.card : ENNReal) / 2 ^ 160 := by
  rw [run_randomizedIndex_fresh_randomizer secretKey pk message cache fresh]
  have bound := probEvent_bind_le_probEvent_add
    (mx := ($ᵗ BitVec 256))
    (my := fun r => do
      let result ← (randomOracle (spec := HashSpec) (indexInput pk message r)).run
        (cache.cacheQuery (randomizerInput secretKey message) r)
      return ((r, result.1.extractLsb' 0 160), result.2))
    (q := fun result => result.1.2 ∈ targets)
    (p := fun r => r ∈ prequeriedRandomizers cache pk message)
    (ε := (targets.card : ENNReal) / 2 ^ 160) (by
      intro r _ notQueried
      have indexFresh : cache (indexInput pk message r) = none := by
        simpa [prequeriedRandomizers] using notQueried
      rw [randomOracle.run_eq, index_cache_after_randomizer, indexFresh]
      simpa only [bind_assoc, pure_bind, ← map_eq_pure_bind, probEvent_map,
        Function.comp_def] using (SecurityUniform.prob_extract_mem 96 160 targets).le)
  rw [SecurityUniform.prob_randomizer_mem] at bound
  exact bound

/-- The exceptional nonce set is no larger than the set of previously queried inputs. -/
theorem prequeriedRandomizers_card_le (cache : QueryCache HashSpec) (pk : PublicKey)
    (message : Message) (inputs : Finset Query)
    (covered : ∀ input, cache input ≠ none → input ∈ inputs) :
    (prequeriedRandomizers cache pk message).card ≤ inputs.card := by
  apply Finset.card_le_card_of_injOn (indexInput pk message)
  · intro r hr
    apply covered
    intro hnone
    simp [prequeriedRandomizers, hnone] at hr
  · intro first _ second _ h
    exact indexInput_randomizer_injective pk message h

/-- The actual fresh randomized-index prefix has the expected linear query bound.
The finite `inputs` may overapproximate all inputs in the shared cache, including
honest program calls; no adversary-only counting convention is used. -/
theorem prob_index_mem_le_queries (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (cache : QueryCache HashSpec) (fresh : cache (randomizerInput secretKey message) = none)
    (inputs : Finset Query) (covered : ∀ input, cache input ≠ none → input ∈ inputs)
    (targets : Finset (BitVec 160)) :
    Pr[fun result => result.1.2 ∈ targets |
      (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (randomizedIndex secretKey pk message)).run cache] ≤
      (inputs.card : ENNReal) / 2 ^ 256 + (targets.card : ENNReal) / 2 ^ 160 := by
  apply (prob_index_mem_le secretKey pk message cache fresh targets).trans
  have hcard := prequeriedRandomizers_card_le cache pk message inputs covered
  gcongr


end SigGolfCandidate.Hypertree.SecurityRandomOracle
