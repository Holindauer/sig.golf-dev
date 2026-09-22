import SigGolfCandidate.Hypertree.SecurityRandomOracle
import SigGolfCandidate.Hypertree.SecurityCache

namespace SigGolfCandidate.Hypertree.SecuritySeed
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityPacking
set_option maxRecDepth 4096

/-- A complete 128-bit seed occurs at the reference derivation input's fixed byte
position. This overapproximates the tag-1 and tag-6 secret-input domains. -/
def SeedAt (input : Query) (seed : Seed) : Prop :=
  ∃ header suffix : List Byte, header.length = 32 ∧
    packed (header ++ bytes seed ++ suffix) = input

/-- Actual seed-derived reference inputs contain the entire seed at this position. -/
theorem seedAt_addressedInput (seed : Seed) (tag level tree leaf chain step : Nat)
    (suffix : List Byte) :
    SeedAt (addressedInput tag level tree leaf chain step (bytes seed ++ suffix)) seed := by
  refine ⟨bytes (n := 8) (BitVec.ofNat 64
    (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32)) ++
      bytes (n := 24) (BitVec.ofNat 192 tree), suffix, ?_, ?_⟩
  · simp [bytes]
  · simp only [addressedInput, List.append_assoc]

theorem seedAt_randomizer (seed : Seed) (message : Message) :
    SeedAt (randomizerInput seed message) seed :=
  seedAt_addressedInput seed 6 0 0 0 0 0 (bytes message)

theorem seedAt_secret (seed : Seed) (level tree leaf chain : Nat) :
    SeedAt (addressedInput 1 level tree leaf chain 0 (bytes seed)) seed := by
  simpa using seedAt_addressedInput seed 1 level tree leaf chain 0 []

/-- One bit-string query can contain at most one seed at the protected position. -/
theorem seedAt_unique {input : Query} {first second : Seed}
    (hfirst : SeedAt input first) (hsecond : SeedAt input second) : first = second := by
  obtain ⟨header, suffix, plen, hp⟩ := hfirst
  obtain ⟨header', suffix', plen', hp'⟩ := hsecond
  have heq := packed_injective (hp.trans hp'.symm)
  rw [List.append_assoc, List.append_assoc] at heq
  have tails := List.append_inj_right heq (plen.trans plen'.symm)
  have seeds := List.append_inj_left tails (by simp [bytes])
  exact bytes_injective 16 seeds

/-- A fixed query independent of the uniform seed guesses it with probability at
most 2^-128. This uses the organizer's actual `sampleSeed`. -/
theorem prob_seedAt_le (input : Query) :
    Pr[SeedAt input | sampleSeed] ≤ 1 / (2 : ENNReal) ^ 128 := by
  classical
  by_cases existsSeed : ∃ seed, SeedAt input seed
  · obtain ⟨seed, hseed⟩ := existsSeed
    have event : SeedAt input = fun other => other = seed := by
      funext other
      exact propext ⟨fun h => seedAt_unique h hseed, fun h => h ▸ hseed⟩
    rw [event]
    rw [probEvent_eq_eq_probOutput]
    unfold sampleSeed
    rw [probOutput_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
    simp only [one_div]
    exact le_rfl
  · have event : SeedAt input = fun _ => False := by
      funext seed
      exact propext ⟨fun h => existsSeed ⟨seed, h⟩, False.elim⟩
    simp [event]

def SeedHitTrace (inputs : List Query) (seed : Seed) : Prop :=
  ∃ input ∈ inputs, SeedAt input seed

/-- Every query is counted, including repetitions; no list-distinctness assumption
or preselected signing-message assumption is hidden in this bound. -/
theorem prob_seedHitTrace_le (inputs : List Query) :
    Pr[SeedHitTrace inputs | sampleSeed] ≤ inputs.length / (2 : ENNReal) ^ 128 := by
  induction inputs with
  | nil => simp [SeedHitTrace]
  | cons input inputs ih =>
    have event : SeedHitTrace (input :: inputs) = fun seed =>
        SeedAt input seed ∨ SeedHitTrace inputs seed := by
      funext seed
      simp [SeedHitTrace]
    rw [event]
    calc
      _ ≤ Pr[SeedAt input | sampleSeed] + Pr[SeedHitTrace inputs | sampleSeed] :=
        probEvent_or_le _ _ _
      _ ≤ 1 / (2 : ENNReal) ^ 128 + inputs.length / (2 : ENNReal) ^ 128 :=
        add_le_add (prob_seedAt_le input) ih
      _ = _ := by simp [Nat.cast_add, ENNReal.add_div, add_comm]

/-- Any distribution of adaptive traces that is independent of the seed has the
same linear guessing bound. The independence requirement is explicit in the
program: the trace is sampled before, and cannot read, `sampleSeed`. -/
theorem prob_independent_trace_seed_le (trace : ProbComp (List Query)) (limit : Nat)
    (bounded : ∀ inputs ∈ support trace, inputs.length ≤ limit) :
    Pr[fun result => SeedHitTrace result.1 result.2 | do
      let inputs ← trace
      let seed ← sampleSeed
      return (inputs, seed)] ≤ limit / (2 : ENNReal) ^ 128 := by
  apply probEvent_bind_le_of_forall_le
  intro inputs hi
  simp only [← map_eq_pure_bind, probEvent_map, Function.comp_def]
  exact (prob_seedHitTrace_le inputs).trans
    (ENNReal.div_le_div (by exact_mod_cast bounded inputs hi) le_rfl)

end SigGolfCandidate.Hypertree.SecuritySeed
