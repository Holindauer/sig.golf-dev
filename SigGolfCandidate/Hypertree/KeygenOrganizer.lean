import SigGolfCandidate.Hypertree.KeygenCache

namespace SigGolfCandidate.Hypertree.KeygenOrganizer
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option maxRecDepth 4096

/-- Every supported lazy-random-oracle result is realized by a single total hash function. -/
theorem fixed_hash_of_support {α : Type} (program : OracleComp HashSpec α) (value : α)
    (mem : value ∈ support (withRandomOracle program)) :
    ∃ hash : Hash, evalWithAnswerFn hash program = value := by
  rw [withRandomOracle,StateT.run'_eq] at mem
  obtain ⟨result,hresult,eq⟩ := mem_support_map_peel Prod.fst _ mem
  obtain ⟨hash,_,heval⟩ := (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support program ∅ value).mpr
    ⟨result.2, by simpa only [eq] using hresult⟩
  exact ⟨hash,heval⟩

theorem eval_keygen (hash : Hash) (secretKey : SecretKey) :
    evalWithAnswerFn hash (submission.run .keygen secretKey) =
      ⟨some (Reference.keygen hash secretKey,KeygenFunctional.zeroCache),true,82446,739,761⟩ :=
  KeygenFunctional.run_exact hash secretKey

/-- An abstract version of the organizer pipeline keeps proof reduction independent of bytecode. -/
def pipeline {σ ω : Type} (keygen : OracleComp HashSpec (RunResult (PublicKey × Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit)) : OracleComp HashSpec HonestResult := do
  let keygen ← keygen
  let costs := recordCost (fun _ => 0) .keygen keygen.hashCompressions
  let some (pk,cache) := keygen.value | return ⟨false,costs,0⟩
  let sign ← sign pk cache
  let costs := recordCost costs .sign sign.hashCompressions
  let some signature := sign.value | return ⟨false,costs,0⟩
  let expand ← expand pk signature
  let costs := recordCost costs .expand expand.hashCompressions
  let some witness := expand.value | return ⟨false,costs,0⟩
  let verify ← verify pk witness
  return ⟨verify.value.isSome,recordCost costs .verify verify.hashCompressions,verify.cycles⟩

theorem pipeline_cost {σ ω : Type} (hash : Hash) (keygen : OracleComp HashSpec (RunResult (PublicKey × Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit)) :
    (evalWithAnswerFn hash (pipeline keygen sign expand verify)).costs .keygen =
      (evalWithAnswerFn hash keygen).hashCompressions := by
  simp only [pipeline,evalWithAnswerFn_bind]
  split <;> simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  · split <;> simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    · split <;> simp [evalWithAnswerFn_pure,recordCost]
    · simp [recordCost]
  · simp [recordCost]

theorem honest_eq_pipeline (s : Submission) (secretKey : SecretKey) (message : Message) :
    s.honest secretKey message = pipeline (s.run .keygen secretKey)
      (fun pk cache => s.run .sign (secretKey,pk,cache,message))
      (fun pk signature => s.run .expand (message,pk,signature))
      (fun pk witness => s.run .verify (message,pk,witness)) := by
  simp only [Submission.honest,pipeline]
  congr 1
  funext kg
  rcases kg.value with _ | ⟨pk,cache⟩
  · rfl
  · dsimp only
    congr 1
    funext sg
    cases sg.value with
    | none => rfl
    | some signature =>
      dsimp only
      congr 1
      funext ex
      cases ex.value with
      | none => rfl
      | some witness => rfl

/-- Later honest phases cannot change the already-recorded key-generation cost. -/
theorem honest_cost (hash : Hash) (secretKey : SecretKey) (message : Message) :
    (evalWithAnswerFn hash (submission.honest secretKey message)).costs .keygen = 761 := by
  have h := pipeline_cost hash (submission.run .keygen secretKey)
    (fun pk cache => submission.run .sign (secretKey,pk,cache,message))
    (fun pk signature => submission.run .expand (message,pk,signature))
    (fun pk witness => submission.run .verify (message,pk,witness))
  have costEq := congrArg (fun result : RunResult (PublicKey × Cache) => result.hashCompressions) (eval_keygen hash secretKey)
  have result := h.trans costEq
  rw [honest_eq_pipeline]
  exact result

/-- The all-message maximum preserves any uniform per-message phase bound. -/
theorem fold_max_cost (hash : Hash) (program : Message → OracleComp HashSpec HonestResult)
    (phase : Phase) (bound : Nat)
    (cost : ∀ message, (evalWithAnswerFn hash (program message)).costs phase ≤ bound)
    (messages : List Message) (initial : HonestSummary) (initialBound : initial.maxCosts phase ≤ bound) :
    (evalWithAnswerFn hash (messages.foldlM (fun summary message => do
      let result ← program message
      return (⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) initial)).maxCosts phase ≤ bound := by
  induction messages generalizing initial with
  | nil => simpa using initialBound
  | cons message messages ih =>
    simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    exact ih _ (max_le initialBound (cost message))

theorem allMessages_cost (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).maxCosts .keygen ≤ 761 := by
  unfold Submission.allMessages
  exact fold_max_cost hash (submission.honest secretKey) .keygen 761
    (fun message => (honest_cost hash secretKey message).le) _ {} (by decide)

theorem support_cost (secretKey : SecretKey) (summary : HonestSummary)
    (mem : summary ∈ support (withRandomOracle (submission.allMessages secretKey))) :
    summary.maxCosts .keygen ≤ 761 := by
  obtain ⟨hash,eq⟩ := fixed_hash_of_support (submission.allMessages secretKey) summary mem
  rw [← eq]
  exact allMessages_cost hash secretKey

/-- The actual organizer exponential-moment inequality for the keygen phase. -/
theorem compression_bound (secretKey : SecretKey) :
    expectedValue (withRandomOracle (submission.allMessages secretKey))
      (fun summary => ENNReal.ofReal (Real.rpow 2
        ((summary.maxCosts .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro summary mem
  have bound : (summary.maxCosts .keygen : ℝ) ≤ 761 := by exact_mod_cast support_cost secretKey summary mem
  have exponent : (summary.maxCosts .keygen : ℝ) / (Phase.keygen.budget : ℝ) ≤ 1 := by
    change (summary.maxCosts .keygen : ℝ) / (1048576 : ℝ) ≤ 1
    apply (div_le_one (by norm_num : (0 : ℝ) < 1048576)).2
    exact bound.trans (by norm_num)
  have power := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) exponent
  rw [Real.rpow_eq_pow]
  simpa only [Real.rpow_one,ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal power

/-- Key generation cannot fail in the actual lazy-random-oracle experiment. -/
theorem keygen_success_probability (secretKey : SecretKey) :
    Pr[fun result => result.value.isSome = true | withRandomOracle (submission.run .keygen secretKey)] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · exact NeverFail.probFailure_eq_zero
  · intro result mem
    obtain ⟨hash,eq⟩ := fixed_hash_of_support (submission.run .keygen secretKey) result mem
    rw [← eq,eval_keygen]
    rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenOrganizer.compression_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compression_bound

end SigGolfCandidate.Hypertree.KeygenOrganizer
