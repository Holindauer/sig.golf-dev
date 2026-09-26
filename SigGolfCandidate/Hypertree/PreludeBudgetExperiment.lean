import SigGolfCandidate.Hypertree.PreludeBudgetAccounting
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def secretKeyedTracked (scheme : Interface) (adversary : Adversary submission.sizes)
    (rounds : Nat) (sk : SecretKey) : OracleComp World (AttackResult × Nat) := do
  let result ← (scheme.keygen sk).liftComp World
  let some (pk,cache) := result.1 | pure (⟨false,result.2⟩,0)
  interactTracked scheme adversary sk pk rounds (adversary.initial pk cache) {hashCalls:=result.2} 0

theorem secretKeyedTracked_base (scheme : Interface) (adversary : Adversary submission.sizes)
    (rounds : Nat) (sk : SecretKey) :
    Prod.fst <$> secretKeyedTracked scheme adversary rounds sk =
      secretKeyedWith scheme adversary rounds sk := by
  simp only [secretKeyedTracked,secretKeyedWith,map_eq_bind_pure_comp,bind_assoc,Function.comp_def]
  apply bind_congr
  intro result
  cases h : result.1 with
  | none => rfl
  | some pair =>
    simpa only [map_eq_bind_pure_comp,Function.comp_def] using
      tracked_base scheme adversary sk pair.1 rounds (adversary.initial pair.1 pair.2) {hashCalls:=result.2} 0

theorem secretKeyedTracked_charged (adversary : Adversary submission.sizes)
    (rounds : Nat) (sk : SecretKey) :
    (fun r => addResultCalls r.1 r.2) <$> secretKeyedTracked baseReferenceInterface adversary rounds sk =
      secretKeyedWith referenceInterface adversary rounds sk := by
  simp only [secretKeyedTracked,secretKeyedWith,map_eq_bind_pure_comp,bind_assoc,Function.comp_def]
  change ((baseReferenceInterface.keygen sk).liftComp World >>= _) =
    ((baseReferenceInterface.keygen sk).liftComp World >>= _)
  apply bind_congr
  intro result
  cases h : result.1 with
  | none => rfl
  | some pair =>
    simpa only [addTranscriptCalls,Nat.add_zero,map_eq_bind_pure_comp,Function.comp_def] using
      tracked_charged adversary sk pair.1 rounds (adversary.initial pair.1 pair.2) {hashCalls:=result.2} 0

theorem observe_map_result {α β : Type} (f : α → β) (program : OracleComp World α)
    (cache : QueryCache HashSpec) :
    observe (f <$> program) cache = f <$> observe program cache := by
  simp [observe]

noncomputable def experimentTracked (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp (AttackResult × Nat) := do
  let sk ← sampleSecretKey
  observe (secretKeyedTracked baseReferenceInterface adversary rounds sk) ∅

theorem experimentTracked_base (adversary : Adversary submission.sizes) (rounds : Nat) :
    Prod.fst <$> experimentTracked adversary rounds =
      experimentWith baseReferenceInterface adversary rounds := by
  rw [experiment_secretKeyed]
  unfold experimentTracked
  rw [map_bind]
  apply bind_congr
  intro sk
  rw [← observe_map_result,secretKeyedTracked_base]

theorem experimentTracked_charged (adversary : Adversary submission.sizes) (rounds : Nat) :
    (fun r => addResultCalls r.1 r.2) <$> experimentTracked adversary rounds =
      experimentWith referenceInterface adversary rounds := by
  rw [experiment_secretKeyed]
  unfold experimentTracked
  rw [map_bind]
  apply bind_congr
  intro sk
  rw [← observe_map_result,secretKeyedTracked_charged]

theorem charged_probability_le_base (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      experimentWith referenceInterface adversary rounds] ≤
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      experimentWith baseReferenceInterface adversary rounds] := by
  rw [← experimentTracked_charged,← experimentTracked_base]
  simp only [probEvent_map,Function.comp_def,addResultCalls]
  apply probEvent_mono
  intro result _ h
  exact ⟨h.1, (Nat.le_add_right result.1.hashCalls result.2).trans h.2⟩

theorem actual_probability_le_base (adversary : Adversary submission.sizes) (rounds budget : Nat) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      Signing.Prelude.preludeSubmission.securityExperiment adversary rounds] ≤
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      experimentWith baseReferenceInterface adversary rounds] := by
  have eq : Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      Signing.Prelude.preludeSubmission.securityExperiment adversary rounds] =
      Pr[fun r => r.won = true ∧ r.hashCalls ≤ budget |
      experimentWith referenceInterface adversary rounds] := by
    simp only [probEvent_def,experiment_equivalent]
  rw [eq]
  exact charged_probability_le_base adversary rounds budget

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.actual_probability_le_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_probability_le_base

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.charged_probability_le_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charged_probability_le_base

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.secretKeyedTracked_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secretKeyedTracked_charged
end SigGolfCandidate.Hypertree.PreludeSecurity
