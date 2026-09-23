import SigGolfCandidate.Hypertree.KeygenOrganizerBridges
import SigGolfCandidate.Hypertree.ExpandCopy
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.Hypertree.KeygenOrganizer
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option maxRecDepth 4096

theorem pipeline_expand_cost {σ ω : Type} (hash : Hash) (keygen : OracleComp HashSpec (RunResult (PublicKey × Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit))
    (zero : ∀ pk signature, (evalWithAnswerFn hash (expand pk signature)).hashCompressions = 0) :
    (evalWithAnswerFn hash (pipeline keygen sign expand verify)).costs .expand = 0 := by
  simp only [pipeline,evalWithAnswerFn_bind]
  split <;> simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  · split <;> simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    · split <;> simp [evalWithAnswerFn_pure,recordCost,zero]
    · simp [recordCost]
  · simp [recordCost]

theorem honest_expand_cost (hash : Hash) (secretKey : SecretKey) (message : Message) :
    (evalWithAnswerFn hash (submission.honest secretKey message)).costs .expand = 0 := by
  rw [honest_eq_pipeline]
  apply pipeline_expand_cost
  intro pk signature
  exact (Expansion.run_bound hash (message,pk,signature)).2.2.2.2

theorem allMessages_expand_cost (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).maxCosts .expand = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Submission.allMessages
  exact fold_max_cost hash (submission.honest secretKey) .expand 0
    (fun message => (honest_expand_cost hash secretKey message).le) _ {} (by decide)

theorem support_expand_cost (secretKey : SecretKey) (summary : HonestSummary)
    (mem : summary ∈ support (withRandomOracle (submission.allMessages secretKey))) :
    summary.maxCosts .expand = 0 := by
  obtain ⟨hash,eq⟩ := fixed_hash_of_support (submission.allMessages secretKey) summary mem
  rw [← eq]
  exact allMessages_expand_cost hash secretKey

/-- Expansion's actual organizer moment is exactly one, because the image makes no hash calls. -/
theorem expansion_compression_moment (secretKey : SecretKey) :
    expectedValue (withRandomOracle (submission.allMessages secretKey))
      (fun summary => ENNReal.ofReal (Real.rpow 2
        ((summary.maxCosts .expand : ℝ) / (Phase.expand.budget : ℝ)))) = 1 := by
  calc
    _ = expectedValue (withRandomOracle (submission.allMessages secretKey)) (fun _ => (1 : ENNReal)) := by
      apply expectedValue_congr_of_support
      intro summary mem
      rw [support_expand_cost secretKey summary mem,Real.rpow_eq_pow]
      simp
    _ = 1 := expectedValue_const NeverFail.probFailure_eq_zero 1

theorem expansion_compression_bound (secretKey : SecretKey) :
    expectedValue (withRandomOracle (submission.allMessages secretKey))
      (fun summary => ENNReal.ofReal (Real.rpow 2
        ((summary.maxCosts .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  rw [expansion_compression_moment]
  norm_num

/-- info: 'SigGolfCandidate.Hypertree.KeygenOrganizer.expansion_compression_moment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms expansion_compression_moment

end SigGolfCandidate.Hypertree.KeygenOrganizer
