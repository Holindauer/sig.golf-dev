import SigGolfCandidate.Hypertree.SecurityIdealSign
import SigGolfCandidate.Hypertree.SecuritySeparation

namespace SigGolfCandidate.Hypertree.SecurityNonce
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityRandomOracle
set_option backward.isDefEq.respectTransparency false

/-- On a first signing request for this message, the private nonce is a fresh full
256-bit uniform. Prior public index queries remain in the public cache unchanged. -/
theorem run_randomizedIndex_fresh (pk : PublicKey) (message : Message) (cache : SplitCache)
    (fresh : cache.1 (.randomizer message) = none) :
    (simulateQ idealOracle (SecurityIdealSign.randomizedIndex pk message)).run cache = do
      let r ← $ᵗ BitVec 256
      let result ← (randomOracle (spec := HashSpec) (indexInput pk message r)).run cache.2
      return ((r, result.1.extractLsb' 0 152),
        (cache.1.cacheQuery (.randomizer message) r, result.2)) := by
  have program : SecurityIdealSign.randomizedIndex pk message = (do
      let r ← liftM (SplitWorld.query (.inl (.randomizer message)))
      let answer ← liftM (SplitWorld.query (.inr (indexInput pk message r)))
      return (r, answer.extractLsb' 0 152)) := rfl
  rw [program]
  simp only [simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, StateT.run_pure]
  simp only [idealOracle, StateT.run, StateT.mk, bind_assoc, pure_bind]
  change ((randomOracle (spec := SecretSpec) (.randomizer message)).run cache.1 >>= _) = _
  rw [randomOracle.run_eq, fresh]
  simp

/-- The actual ideal signing prefix hits a previously designated index only through
a prequeried randomizer or a fresh 152-bit target hit. The state and target set may
be chosen adaptively before this first request for the message. -/
theorem prob_index_mem_le (pk : PublicKey) (message : Message) (cache : SplitCache)
    (fresh : cache.1 (.randomizer message) = none) (targets : Finset (BitVec 152)) :
    Pr[fun result => result.1.2 ∈ targets |
      (simulateQ idealOracle (SecurityIdealSign.randomizedIndex pk message)).run cache] ≤
        ((prequeriedRandomizers cache.2 pk message).card : ENNReal) / 2 ^ 256 +
          (targets.card : ENNReal) / 2 ^ 152 := by
  rw [run_randomizedIndex_fresh pk message cache fresh]
  have bound := probEvent_bind_le_probEvent_add
    (mx := ($ᵗ BitVec 256))
    (my := fun r => do
      let result ← (randomOracle (spec := HashSpec) (indexInput pk message r)).run cache.2
      return ((r, result.1.extractLsb' 0 152),
        (cache.1.cacheQuery (.randomizer message) r, result.2)))
    (q := fun result => result.1.2 ∈ targets)
    (p := fun r => r ∈ prequeriedRandomizers cache.2 pk message)
    (ε := (targets.card : ENNReal) / 2 ^ 152) (by
      intro r _ notQueried
      have indexFresh : cache.2 (indexInput pk message r) = none := by
        simpa [prequeriedRandomizers] using notQueried
      rw [randomOracle.run_eq, indexFresh]
      simpa only [bind_assoc, pure_bind, ← map_eq_pure_bind, probEvent_map,
        Function.comp_def] using (SecurityUniform.prob_extract_mem 104 152 targets).le)
  rw [SecurityUniform.prob_randomizer_mem] at bound
  exact bound

end SigGolfCandidate.Hypertree.SecurityNonce
