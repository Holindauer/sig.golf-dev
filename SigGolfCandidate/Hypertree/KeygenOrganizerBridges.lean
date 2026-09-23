import SigGolfCandidate.Hypertree.KeygenOrganizer

namespace SigGolfCandidate.Hypertree.KeygenOrganizer
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option maxRecDepth 4096

/-- Uniform deterministic phase costs bound the uniform-message, random-oracle moment. -/
theorem compression_of_honest_cost (candidate : Submission) (phase : Phase)
    (positive : 0 < phase.budget)
    (bounded : ∀ hash secretKey message,
      (evalWithAnswerFn hash (candidate.honest secretKey message)).costs phase ≤ phase.budget)
    (secretKey : SecretKey) :
    expectedValue (candidate.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2 ((result.costs phase : ℝ) / (phase.budget : ℝ)))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro result mem
  unfold Submission.honestWorkload at mem
  obtain ⟨message, _, inOracle⟩ := (mem_support_bind_iff _ _ _).mp mem
  obtain ⟨hash, eq⟩ := fixed_hash_of_support (candidate.honest secretKey message) result inOracle
  have costBound : result.costs phase ≤ phase.budget := by
    rw [← eq]
    exact bounded hash secretKey message
  have denom : (0 : ℝ) < phase.budget := by exact_mod_cast positive
  have exponent : (result.costs phase : ℝ) / (phase.budget : ℝ) ≤ 1 := by
    apply (div_le_one denom).2
    exact_mod_cast costBound
  rw [Real.rpow_eq_pow]
  simpa only [Real.rpow_one, ENNReal.ofReal_ofNat] using
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) exponent)

/-- Assemble all budgeted phases once their honest deterministic cost bounds are proved. -/
theorem compressionBounds_of_honest_cost (candidate : Submission)
    (bounded : ∀ hash secretKey message phase, phase ∈ Phase.budgeted →
      (evalWithAnswerFn hash (candidate.honest secretKey message)).costs phase ≤ phase.budget) :
    candidate.CompressionBounds := by
  intro secretKey phase mem
  apply compression_of_honest_cost candidate phase
  · cases phase <;> simp_all [Phase.budgeted,Phase.budget,BUDGET_KEYGEN,BUDGET_SIGN,BUDGET_EXPAND]
  · intro hash secretKey message
    exact bounded hash secretKey message phase mem


theorem fold_all_succeed (hash : Hash) (program : Message → OracleComp HashSpec HonestResult)
    (success : ∀ message, (evalWithAnswerFn hash (program message)).success = true)
    (messages : List Message) (initial : HonestSummary) (initialGood : initial.allSucceed = true) :
    (evalWithAnswerFn hash (messages.foldlM (fun summary message => do
      let result ← program message
      return (⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) initial)).allSucceed = true := by
  induction messages generalizing initial with
  | nil => simpa using initialGood
  | cons message messages ih =>
    simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    exact ih _ (by simp only [initialGood,success message,Bool.true_and])

/-- This bridge has an explicit premise: bytecode correctness must first prove every honest pipeline succeeds. -/
theorem complete_of_honest_success (candidate : Submission)
    (success : ∀ hash secretKey message, (evalWithAnswerFn hash (candidate.honest secretKey message)).success = true) :
    candidate.Complete := by
  intro secretKey
  have certain : Pr[fun summary => summary.allSucceed = true | withRandomOracle (candidate.allMessages secretKey)] = 1 := by
    rw [probEvent_eq_one_iff]
    refine ⟨NeverFail.probFailure_eq_zero,?_⟩
    intro summary mem
    obtain ⟨hash,eq⟩ := fixed_hash_of_support (candidate.allMessages secretKey) summary mem
    rw [← eq]
    unfold Submission.allMessages
    exact fold_all_succeed hash (candidate.honest secretKey) (success hash secretKey) _ {} rfl
  rw [certain]
  exact tsub_le_self

/-- info: 'SigGolfCandidate.Hypertree.KeygenOrganizer.complete_of_honest_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_of_honest_success

end SigGolfCandidate.Hypertree.KeygenOrganizer
