import SigGolfCandidate.Hypertree.SecurityRandomOracle
import SigGolfCandidate.Hypertree.SecurityCache

namespace SigGolfCandidate.Hypertree.SecuritySecretKey
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityPacking
set_option maxRecDepth 4096

/-- A complete 256-bit secret key occurs at the reference derivation input's fixed byte
position. This overapproximates the tag-1 and tag-6 secret-input domains. -/
def SecretKeyAt (input : Query) (secretKey : SecretKey) : Prop :=
  ∃ header suffix : List Byte, header.length = 32 ∧
    packed (header ++ bytes secretKey ++ suffix) = input

/-- Actual secret key-derived reference inputs contain the entire secret key at this position. -/
theorem secretKeyAt_addressedInput (secretKey : SecretKey) (tag level tree leaf chain step : Nat)
    (suffix : List Byte) :
    SecretKeyAt (addressedInput tag level tree leaf chain step (bytes secretKey ++ suffix)) secretKey := by
  refine ⟨bytes (n := 8) (BitVec.ofNat 64
    (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32)) ++
      bytes (n := 24) (BitVec.ofNat 192 tree), suffix, ?_, ?_⟩
  · simp [bytes]
  · simp only [addressedInput, List.append_assoc]

theorem secretKeyAt_randomizer (secretKey : SecretKey) (message : Message) :
    SecretKeyAt (randomizerInput secretKey message) secretKey :=
  secretKeyAt_addressedInput secretKey 6 0 0 0 0 0 (bytes message)

theorem secretKeyAt_secret (secretKey : SecretKey) (level tree leaf chain : Nat) :
    SecretKeyAt (addressedInput 1 level tree leaf chain 0 (bytes secretKey)) secretKey := by
  simpa using secretKeyAt_addressedInput secretKey 1 level tree leaf chain 0 []

/-- One bit-string query can contain at most one secret key at the protected position. -/
theorem secretKeyAt_unique {input : Query} {first second : SecretKey}
    (hfirst : SecretKeyAt input first) (hsecond : SecretKeyAt input second) : first = second := by
  obtain ⟨header, suffix, plen, hp⟩ := hfirst
  obtain ⟨header', suffix', plen', hp'⟩ := hsecond
  have heq := packed_injective (hp.trans hp'.symm)
  rw [List.append_assoc, List.append_assoc] at heq
  have tails := List.append_inj_right heq (plen.trans plen'.symm)
  have secretKeys := List.append_inj_left tails (by simp [bytes])
  exact bytes_injective 32 secretKeys

/-- A fixed query independent of the uniform 256-bit secret key guesses it with
probability at most 2^-256. This uses the organizer's actual `sampleSecretKey`. -/
theorem prob_secretKeyAt_le_256 (input : Query) :
    Pr[SecretKeyAt input | sampleSecretKey] ≤ 1 / (2 : ENNReal) ^ 256 := by
  classical
  by_cases existsSecretKey : ∃ secretKey, SecretKeyAt input secretKey
  · obtain ⟨secretKey, hsecretKey⟩ := existsSecretKey
    have event : SecretKeyAt input = fun other => other = secretKey := by
      funext other
      exact propext ⟨fun h => secretKeyAt_unique h hsecretKey, fun h => h ▸ hsecretKey⟩
    rw [event]
    rw [probEvent_eq_eq_probOutput]
    unfold sampleSecretKey
    rw [probOutput_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
    simp only [one_div]
    exact le_rfl
  · have event : SecretKeyAt input = fun _ => False := by
      funext secretKey
      exact propext ⟨fun h => existsSecretKey ⟨secretKey, h⟩, False.elim⟩
    simp [event]

/-- The security reduction uses the weaker 128-bit allocation shared with its
independent 128-bit hash-target collision event. -/
theorem prob_secretKeyAt_le (input : Query) :
    Pr[SecretKeyAt input | sampleSecretKey] ≤ 1 / (2 : ENNReal) ^ 128 :=
  (prob_secretKeyAt_le_256 input).trans (ENNReal.div_le_div le_rfl (by norm_num))

def SecretKeyHitTrace (inputs : List Query) (secretKey : SecretKey) : Prop :=
  ∃ input ∈ inputs, SecretKeyAt input secretKey

/-- Every query is counted, including repetitions; no list-distinctness assumption
or preselected signing-message assumption is hidden in this bound. -/
theorem prob_secretKeyHitTrace_le (inputs : List Query) :
    Pr[SecretKeyHitTrace inputs | sampleSecretKey] ≤ inputs.length / (2 : ENNReal) ^ 128 := by
  induction inputs with
  | nil => simp [SecretKeyHitTrace]
  | cons input inputs ih =>
    have event : SecretKeyHitTrace (input :: inputs) = fun secretKey =>
        SecretKeyAt input secretKey ∨ SecretKeyHitTrace inputs secretKey := by
      funext secretKey
      simp [SecretKeyHitTrace]
    rw [event]
    calc
      _ ≤ Pr[SecretKeyAt input | sampleSecretKey] + Pr[SecretKeyHitTrace inputs | sampleSecretKey] :=
        probEvent_or_le _ _ _
      _ ≤ 1 / (2 : ENNReal) ^ 128 + inputs.length / (2 : ENNReal) ^ 128 :=
        add_le_add (prob_secretKeyAt_le input) ih
      _ = _ := by simp [Nat.cast_add, ENNReal.add_div, add_comm]

/-- Any distribution of adaptive traces that is independent of the secret key has the
same linear guessing bound. The independence requirement is explicit in the
program: the trace is sampled before, and cannot read, `sampleSecretKey`. -/
theorem prob_independent_trace_secretKey_le (trace : ProbComp (List Query)) (limit : Nat)
    (bounded : ∀ inputs ∈ support trace, inputs.length ≤ limit) :
    Pr[fun result => SecretKeyHitTrace result.1 result.2 | do
      let inputs ← trace
      let secretKey ← sampleSecretKey
      return (inputs, secretKey)] ≤ limit / (2 : ENNReal) ^ 128 := by
  apply probEvent_bind_le_of_forall_le
  intro inputs hi
  simp only [← map_eq_pure_bind, probEvent_map, Function.comp_def]
  exact (prob_secretKeyHitTrace_le inputs).trans
    (ENNReal.div_le_div (by exact_mod_cast bounded inputs hi) le_rfl)

end SigGolfCandidate.Hypertree.SecuritySecretKey
