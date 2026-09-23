import SigGolfCandidate.Hypertree.SecurityGameHop
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyMonitor
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecuritySecretKey SecurityDerivation SecuritySeparation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Charge only public inputs in an actual secret key-derivation domain. Repeated
calls remain repeated entries, matching the organizer's call accounting. -/
noncomputable def eligible (inputs : List Query) : List Query := inputs.filter (fun input => decide (SecretKeyEligible input))

@[simp] theorem mem_eligible (input : Query) (inputs : List Query) :
    input ∈ eligible inputs ↔ input ∈ inputs ∧ SecretKeyEligible input := by simp [eligible]

/-- The secret key is tested against a fixed trace but is never supplied to its producer. -/
def Hit (inputs : List Query) (secretKey : SecretKey) : Prop := SecretKeyHitTrace (eligible inputs) secretKey

theorem hit_iff (inputs : List Query) (secretKey : SecretKey) :
    Hit inputs secretKey ↔ ∃ input ∈ inputs, publicSecretKeyHit secretKey (.inr input) := by
  simp only [Hit, SecretKeyHitTrace, mem_eligible, publicSecretKeyHit]
  constructor
  · rintro ⟨input, ⟨member, domain⟩, atSecretKey⟩
    exact ⟨input, member, domain, atSecretKey⟩
  · rintro ⟨input, member, domain, atSecretKey⟩
    exact ⟨input, ⟨member, domain⟩, atSecretKey⟩

/-- A secret key-eligible query has a unique full secret key candidate. -/
noncomputable def candidate (input : Query) : Option SecretKey :=
  if domain : SecretKeyEligible input then some domain.choose else none

private theorem secretKeyAt_transport (secretKey : SecretKey) (slot : Slot) (query : Query)
    (same : SecurityDerivation.input secretKey slot = query) : SecretKeyAt query secretKey :=
  same ▸ input_secretKeyAt secretKey slot

theorem candidate_some_iff (input : Query) (secretKey : SecretKey) :
    candidate input = some secretKey ↔ publicSecretKeyHit secretKey (.inr input) := by
  unfold candidate
  split
  next domain =>
    have atSecretKey : SecretKeyAt input domain.choose := by
      obtain ⟨slot, same⟩ := domain.choose_spec
      exact secretKeyAt_transport domain.choose slot input same
    constructor
    · intro same
      exact ⟨domain, Option.some.inj same ▸ atSecretKey⟩
    · intro hit
      exact congrArg some (secretKeyAt_unique atSecretKey hit.2)
  next outside => simp only [reduceCtorEq, publicSecretKeyHit, outside, false_and]

@[simp] theorem candidate_none_iff (input : Query) : candidate input = none ↔ ¬SecretKeyEligible input := by
  simp [candidate]

theorem hit_candidates (inputs : List Query) (secretKey : SecretKey) :
    Hit inputs secretKey ↔ secretKey ∈ inputs.filterMap candidate := by
  rw [hit_iff, List.mem_filterMap]
  simp only [candidate_some_iff]

theorem candidate_count (inputs : List Query) :
    (inputs.filterMap candidate).length = (eligible inputs).length := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    by_cases domain : SecretKeyEligible input <;>
      simp [candidate, eligible, domain] at * <;> exact ih

@[simp] theorem eligible_idempotent (inputs : List Query) : eligible (eligible inputs) = eligible inputs := by
  simp [eligible]

structure Outcome (α : Type) where
  value : α
  secretKey : SecretKey
  bad : Bool
  calls : Nat

/-- The unchanged sampled view can contain final adversary output, all other
passive flags, and all other query counters. Only this annotation reads the secret key. -/
noncomputable def annotate {α : Type} (inputs : α → List Query) (value : α) (secretKey : SecretKey) : Outcome α :=
  ⟨value, secretKey, decide (Hit (inputs value) secretKey), (eligible (inputs value)).length⟩

noncomputable def experiment {α : Type} (draw : ProbComp α) (inputs : α → List Query) : ProbComp (Outcome α) := do
  let value ← draw
  let secretKey ← sampleSecretKey
  pure (annotate inputs value secretKey)

/-- The same joint experiment can sample its uniform secret key first, provided that
its common simulation does not read the secret key. -/
theorem secretKey_first {α : Type} (draw : ProbComp α) (inputs : α → List Query) :
    𝒮[experiment draw inputs] =
      𝒮[do let secretKey ← sampleSecretKey; let value ← draw; pure (annotate inputs value secretKey)] :=
  evalSPMF_bind_bind_swap _ _ _

/-- All original outputs and counters are retained with their exact joint law. -/
theorem value_projection {α : Type} (draw : ProbComp α) (inputs : α → List Query) :
    𝒮[Outcome.value <$> experiment draw inputs] = 𝒮[draw] := by
  classical
  simp only [experiment, map_bind, map_pure, annotate]
  have step (value : α) : 𝒮[do let _ ← sampleSecretKey; pure value] = 𝒮[(pure value : ProbComp α)] := by
    apply evalSPMF_ext
    intro output
    rw [probOutput_bind_const]
    rw [NeverFail.probFailure_eq_zero]
    simp only [tsub_zero, one_mul]
  have same := evalSPMF_bind_congr (mx := draw)
    (ob₁ := fun value => do let _ ← sampleSecretKey; pure value)
    (ob₂ := fun value => pure value) (fun value _ => step value)
  simpa only [bind_pure] using same

/-- Every event of the retained common view has exactly its original probability. -/
theorem value_event {α : Type} (draw : ProbComp α) (inputs : α → List Query) (event : α → Prop) :
    Pr[fun result => event result.value | experiment draw inputs] = Pr[event | draw] := by
  have same := probEvent_congr' (p := event) (q := event) (fun _ _ => Iff.rfl)
    (value_projection draw inputs)
  rw [probEvent_map] at same
  exact same

/-- Expectations of all other counters are preserved in the same joint experiment. -/
theorem expected_value {α : Type} (draw : ProbComp α) (inputs : α → List Query) (work : α → ENNReal) :
    expectedValue (experiment draw inputs) (fun result => work result.value) = expectedValue draw work := by
  have same : expectedValue (Outcome.value <$> experiment draw inputs) work = expectedValue draw work := by
    apply expectedValue_congr _ work
    intro value
    exact probOutput_congr rfl (value_projection draw inputs)
  rw [expectedValue_map] at same
  exact same

/-- Exact mean of the secret key-query class in the same joint output distribution. -/
theorem expected_calls {α : Type} (draw : ProbComp α) (inputs : α → List Query) :
    expectedValue (experiment draw inputs) (fun result => (result.calls : ENNReal)) =
      expectedValue draw (fun value => ((eligible (inputs value)).length : ENNReal)) := by
  simp only [experiment, expectedValue_bind, expectedValue_pure, annotate,
    expectedValue_const NeverFail.probFailure_eq_zero]

/-- One common simulation supplies both the secret key-contact event and its charged
calls. This does not transfer an expectation across a prior game hop. -/
theorem prob_bad_le_expected {α : Type} (draw : ProbComp α) (inputs : α → List Query) :
    Pr[fun result => result.bad = true | experiment draw inputs] ≤
      expectedValue (experiment draw inputs) (fun result => (result.calls : ENNReal)) / (2 : ENNReal)^128 := by
  rw [expected_calls]
  simp only [experiment, probEvent_bind_eq_expectedValue, probEvent_pure, annotate, decide_eq_true_eq]
  calc
    _ ≤ expectedValue draw (fun value => ((eligible (inputs value)).length : ENNReal) / (2 : ENNReal)^128) := by
      apply expectedValue_mono
      intro value
      simpa only [expectedValue_ite_one, Hit] using
        prob_secretKeyHitTrace_le (eligible (inputs value))
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

/-- Weighted allowance form for combination with the other disjoint query classes. -/
theorem prob_bad_le_allowance {α : Type} (draw : ProbComp α) (inputs : α → List Query)
    (allowance : ENNReal)
    (work : expectedValue (experiment draw inputs) (fun result => (result.calls : ENNReal)) ≤ allowance) :
    Pr[fun result => result.bad = true | experiment draw inputs] ≤ allowance / (2 : ENNReal)^128 :=
  (prob_bad_le_expected draw inputs).trans (ENNReal.div_le_div work le_rfl)

/-- A joint union bound with any event of the common simulator, with both
expectations evaluated under this single output-retaining experiment. -/
theorem prob_union_le {α : Type} (draw : ProbComp α) (inputs : α → List Query) (event : α → Prop) :
    Pr[fun result => event result.value ∨ result.bad = true | experiment draw inputs] ≤
      Pr[event | draw] + expectedValue (experiment draw inputs)
        (fun result => (result.calls : ENNReal)) / (2 : ENNReal)^128 := by
  calc
    _ ≤ Pr[fun result => event result.value | experiment draw inputs] +
        Pr[fun result => result.bad = true | experiment draw inputs] := probEvent_or_le _ _ _
    _ ≤ _ := by rw [value_event]; exact add_le_add le_rfl (prob_bad_le_expected draw inputs)

end SigGolfCandidate.Hypertree.SecuritySecretKeyMonitor
