import SigGolfCandidate.Hypertree.SecurityGraphQuery
import SigGolfCandidate.Hypertree.SecurityExtraction

namespace SigGolfCandidate.Hypertree.SecurityGraphContact
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityExtraction SecurityPacking
open scoped Classical

/-- Exact chain-hash input as a function of its 128-bit predecessor. -/
def chainInput (address : ChainAddress) (step : Fin 7) (point : Digest) : Query :=
  (Position.chain address step).address.input (bytes point)

theorem chainInput_injective (address : ChainAddress) (step : Fin 7) :
    Function.Injective (chainInput address step) := by
  intro first second equal
  apply bytes_injective 16
  exact addressedInput_payload_injective _ _ _ _ _ _ equal

/-- Guessing a fresh hidden chain predecessor has probability at most 2^-128,
even for a malformed or wrong-address query. -/
theorem prob_chain_input_guess (address : ChainAddress) (step : Fin 7) (query : Query) :
    Pr[fun value : BitVec 256 => query = chainInput address step (truncate value) |
      $ᵗ BitVec 256] ≤ 1 / 2 ^ 128 := by
  by_cases possible : ∃ point, query = chainInput address step point
  · obtain ⟨point, equal⟩ := possible
    have event : (fun value : BitVec 256 => query = chainInput address step (truncate value)) =
        (fun value => value.extractLsb' 0 128 ∈ ({point} : Finset Digest)) := by
      funext value
      apply propext
      simp only [Finset.mem_singleton]
      constructor
      · intro matched
        exact (chainInput_injective address step (equal.symm.trans matched)).symm
      · intro matched
        exact equal.trans (congrArg (chainInput address step) matched.symm)
    rw [event, SecurityUniform.prob_extract_mem 128 128]
    simp
  · have event : (fun value : BitVec 256 => query = chainInput address step (truncate value)) =
        (fun _ => False) := by
      funext value
      apply propext
      exact ⟨fun equal => possible ⟨truncate value, equal⟩, False.elim⟩
    rw [event]
    simp

/-- One real lazy-oracle call with an independently hidden canonical chain input.
Both hitting that input and obtaining its truncated target output count as contact. -/
noncomputable def chainTrial (address : ChainAddress) (step : Fin 7) (query : Query)
    (target : BitVec 256) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let hidden ← $ᵗ BitVec 256
  let canonical := chainInput address step (truncate hidden)
  let result ← (randomOracle (spec := HashSpec) query).run (cache.cacheQuery canonical target)
  return decide (query = canonical ∨ truncate result.1 = truncate target)

/-- The correct local chain hazard is at most 2/2^128: one predecessor guess and
one independent output collision. The old 1/2^128 allocation would miss the first
case. Global use still requires a proved adaptive hidden-coordinate invariant. -/
theorem prob_chain_contact_le (address : ChainAddress) (step : Fin 7) (query : Query)
    (target : BitVec 256) (cache : QueryCache HashSpec) (fresh : cache query = none) :
    Pr[fun hit => hit = true | chainTrial address step query target cache] ≤ 2 / 2 ^ 128 := by
  unfold chainTrial
  have bound := probEvent_bind_le_probEvent_add
    (mx := ($ᵗ BitVec 256))
    (my := fun hidden => do
      let canonical := chainInput address step (truncate hidden)
      let result ← (randomOracle (spec := HashSpec) query).run (cache.cacheQuery canonical target)
      return decide (query = canonical ∨ truncate result.1 = truncate target))
    (q := fun hit => hit = true)
    (p := fun hidden => query = chainInput address step (truncate hidden))
    (ε := (1 : ENNReal) / 2 ^ 128) (by
      intro hidden _ different
      dsimp only
      rw [randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ different, fresh]
      simp only [bind_assoc, pure_bind]
      have exactProbability := SecurityUniform.prob_extract_mem 128 128 ({truncate target} : Finset Digest)
      simp only [← map_eq_pure_bind, probEvent_map, Function.comp_def]
      change Pr[fun value : BitVec 256 => decide (query = chainInput address step (truncate hidden) ∨
        truncate value = truncate target) = true | $ᵗ BitVec 256] ≤ _
      simp only [different, false_or, decide_eq_true_eq]
      simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one,
        truncate] using exactProbability.le)
  calc
    _ ≤ Pr[fun value : BitVec 256 => query = chainInput address step (truncate value) |
          $ᵗ BitVec 256] + 1 / 2 ^ 128 := bound
    _ ≤ 1 / 2 ^ 128 + 1 / 2 ^ 128 :=
      add_le_add (prob_chain_input_guess address step query) le_rfl
    _ = _ := by simp only [div_eq_mul_inv]; ring

end SigGolfCandidate.Hypertree.SecurityGraphContact
