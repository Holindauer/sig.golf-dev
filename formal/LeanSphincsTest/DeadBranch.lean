import LeanSphincs.Benchmark.Target

/-! Regression fixture: probability-zero query padding. Not a signature scheme.

`cheat` accepts every signature. Its key generation hashes the empty input twice
and pads with 2^128 empty-input queries only when the two answers differ. Under the
lazy random oracle that branch never runs (`keygen_runtime`), yet the structural
`HasHashQueryBound` hypothesis forces every admissible budget past 2^128, which
makes the security clause and both adaptive availability clauses vacuous. Every
clause of `SchemeClaim` except the structural keygen cap is therefore provable
(`almost_claim`); the cap rejects it (`rejected`, `no_claim`). -/

open OracleComp OracleSpec LeanSphincs.Benchmark ENNReal

namespace LeanSphincsTest.DeadBranch

def hashQ (input : Bytes) : OracleComp OracleWorld HashOutput :=
  liftM (OracleWorld.query (Sum.inr input))

/-- `n` raw empty-input hash queries; each has zero weighted verification cost. -/
def pad : Nat → OracleComp OracleWorld Unit
  | 0 => pure ()
  | n + 1 => do
    let _ ← hashQ []
    pad n

def padBudget : Nat := 2 ^ 128

def deadBranch : OracleComp OracleWorld Unit := do
  let a ← hashQ []
  let b ← hashQ []
  if a = b then pure () else pad padBudget

noncomputable def cheat : SigScheme where
  SecretKey := Unit
  keygen := do
    deadBranch
    pure ([], ())
  sign := fun _ _ => pure (some [0])
  verify := fun _ _ _ => pure true

def coeffs : BoundCoeffs := [⟨1, 0, 1, 0, 128⟩]

theorem pad_forces {β : Type} {p : ℕ ⊕ Bytes → Prop} [DecidablePred p]
    (hp : p (Sum.inr [])) :
    ∀ (N : ℕ) (k : Unit → OracleComp OracleWorld β) (n : ℕ),
      IsQueryBoundP (pad N >>= k) p n → N ≤ n := by
  intro N
  induction N with
  | zero => intro _ _ _; exact Nat.zero_le _
  | succ N ih =>
    intro k n h
    have h' : IsQueryBoundP (liftM (OracleWorld.query (Sum.inr ([] : Bytes))) >>=
        fun _ => pad N >>= k) p n := by
      rw [← bind_assoc]; exact h
    rw [isQueryBoundP_query_bind_iff] at h'
    obtain ⟨hpos, hrest⟩ := h'
    have hn : 0 < n := hpos.resolve_left (not_not.mpr hp)
    have hih := ih k _ (hrest (BitVec.ofNat 256 0))
    rw [if_pos hp] at hih
    omega

/-- The inconsistent-answer path exists structurally and carries the padding. -/
theorem deadBranch_forces {β : Type} {p : ℕ ⊕ Bytes → Prop} [DecidablePred p]
    (hp : p (Sum.inr [])) (k : Unit → OracleComp OracleWorld β) (n : ℕ)
    (h : IsQueryBoundP (deadBranch >>= k) p n) : padBudget ≤ n := by
  simp only [deadBranch, hashQ, bind_assoc] at h
  obtain ⟨_, h2⟩ := (isQueryBoundP_query_bind_iff p _ _ n).mp h
  have h2 := h2 (BitVec.ofNat 256 0)
  rw [if_pos hp] at h2
  obtain ⟨_, h3⟩ := (isQueryBoundP_query_bind_iff p _ _ _).mp h2
  have h3 := h3 (BitVec.ofNat 256 1)
  rw [if_pos hp] at h3
  have hne : (BitVec.ofNat 256 0 : HashOutput) ≠ BitVec.ofNat 256 1 := by decide
  simp only [hne, if_false] at h3
  have := pad_forces hp padBudget k _ h3
  omega

theorem hashBound_forces (A : Adversary) (qH : ℕ) (h : HasHashQueryBound cheat A qH) :
    padBudget ≤ qH := by
  unfold HasHashQueryBound gameCore at h
  simp only [cheat, bind_assoc] at h
  exact deadBranch_forces (by simp) _ _ h

theorem interactionBound_forces (A : SigningParticipant) (qH : ℕ)
    (h : HasInteractionHashBound cheat A qH) : padBudget ≤ qH := by
  unfold HasInteractionHashBound signingInteraction at h
  simp only [cheat, bind_assoc] at h
  exact deadBranch_forces (by simp) _ _ h

theorem runROM_bind_const {α β : Type} (oa : OracleComp OracleWorld α) (c : β) :
    runROM (oa >>= fun _ => pure c) = (fun _ => c) <$> runROM oa := by
  simp [runROM, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

/-- Under the lazy random oracle, keygen is one uniform sample and no padding:
the branch is absent from the ROM semantics, so no runtime metric can observe it. -/
theorem keygen_runtime :
    runROM cheat.keygen =
      (fun _ : HashOutput => (([] : Bytes), ())) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
  have h1 : simulateQ romImpl (hashQ []) =
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) [] := by
    simp [hashQ, romImpl]
  simp only [runROM, cheat, deadBranch, simulateQ_bind, simulateQ_pure, h1, bind_assoc]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure]
  rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  simp only [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
  simp only [uniformSampleImpl, Function.comp_def]
  rfl

theorem correct : CorrectOnSuccess cheat := by
  intro message
  have h : correctnessExperiment cheat message = deadBranch >>= fun _ => pure true := by
    simp [correctnessExperiment, cheat]
  rw [h, runROM_bind_const]
  refine probOutput_eq_one_of_support_subset_singleton (probFailure_of_liftM_PMF _) ?_
  intro y hy
  rw [support_map, Set.mem_image] at hy
  obtain ⟨_, _, h⟩ := hy
  exact h.symm

theorem signing_failure : HasSigningFailureBound cheat signingFailureBits := by
  intro message
  have h : signingFailureExperiment cheat message = deadBranch >>= fun _ => pure false := by
    simp [signingFailureExperiment, cheat]
  rw [h, runROM_bind_const]
  have : Pr[= true | (fun _ => false) <$> runROM deadBranch] = 0 := by
    apply probOutput_eq_zero_of_not_mem_support
    simp [support_map]
  rw [this]
  simp

/-- Both adaptive clauses assume `qH + qS <= work` with a structural hash bound
that the dead branch contradicts, so they hold vacuously. -/
theorem adaptive_vacuous (cap work : ℕ) (hw : work < padBudget) :
    HasAdaptiveSigningFailureBound cheat cap work signingFailureBits := by
  intro A qH qS _ hwork hh _ _ _
  have := interactionBound_forces A qH hh
  omega

/-- The padding is pure hashing: no path draws uniform randomness. -/
theorem pad_noSample : ∀ N, IsQueryBoundP (pad N) (· matches (Sum.inl _ : ℕ ⊕ Bytes)) 0 := by
  intro N
  induction N with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ N ih =>
    have h : IsQueryBoundP (liftM (OracleWorld.query (Sum.inr ([] : Bytes))) >>= fun _ => pad N)
        (· matches (Sum.inl _ : ℕ ⊕ Bytes)) 0 := by
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by decide), fun _ => ?_⟩
      rw [if_neg (by decide)]
      exact ih
    exact h

theorem deadBranch_noSample :
    IsQueryBoundP deadBranch (· matches (Sum.inl _ : ℕ ⊕ Bytes)) 0 := by
  have h : IsQueryBoundP (liftM (OracleWorld.query (Sum.inr ([] : Bytes))) >>= fun a =>
      liftM (OracleWorld.query (Sum.inr ([] : Bytes))) >>= fun b =>
        (if a = b then pure () else pad padBudget))
      (· matches (Sum.inl _ : ℕ ⊕ Bytes)) 0 := by
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by decide), fun a => ?_⟩
    rw [if_neg (by decide), isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by decide), fun b => ?_⟩
    by_cases hab : a = b
    · rw [if_pos hab]; exact isQueryBoundP_pure _ _ _
    · rw [if_neg hab]; exact pad_noSample padBudget
  exact h

theorem keygen_samples : HasKeygenSampleBound cheat sampleKeygenCap := by
  have key : IsQueryBoundP (deadBranch >>= fun _ => pure (([] : Bytes), ()))
      (· matches (Sum.inl _ : ℕ ⊕ Bytes)) (0 + 0) :=
    isQueryBoundP_bind deadBranch_noSample (fun _ _ => isQueryBoundP_pure _ _ _)
  exact key.mono (Nat.zero_le sampleKeygenCap)

theorem sign_samples : HasSignSampleBound cheat sampleSignCap :=
  fun _ _ => isQueryBoundP_pure _ _ _

theorem sigma_size : HasSignatureSize cheat 1 := by
  intro _ _ _ signature h
  have h' := OracleComp.eq_of_mem_support_pure _ h
  simp only [Option.some.injEq] at h'
  subst h'
  rfl

theorem public_key_size : HasPublicKeySize cheat 32 := by
  intro keys hk
  simp only [cheat] at hk
  obtain ⟨_, _, hk⟩ := (mem_support_bind_iff _ _ _).mp hk
  have := OracleComp.eq_of_mem_support_pure _ hk
  subst this
  simp

/-- The security clause collapses to `Adv <= 1 <= Q / 2^128` without any forgery argument. -/
theorem security_vacuous (A : Adversary) (qH qS : ℕ)
    (hH : HasHashQueryBound cheat A qH) :
    sufAdvantage cheat A ≤ boundProbability coeffs (qH + qS) qS := by
  have hK : padBudget ≤ qH := hashBound_forces A qH hH
  calc sufAdvantage cheat A ≤ 1 := probOutput_le_one
    _ ≤ boundProbability coeffs (qH + qS) qS := by
      unfold boundProbability
      rw [ENNReal.one_le_ofReal]
      have hq : (1 : ℚ) ≤ evalBound coeffs ((qH + qS : ℕ) : ℚ) qS := by
        have h2 : ((2 : ℚ) ^ 128) ≤ ((qH + qS : ℕ) : ℚ) := by
          have : 2 ^ 128 ≤ qH + qS := le_trans hK (Nat.le_add_right _ _)
          exact_mod_cast this
        have hpos : (0 : ℚ) < 2 ^ 128 := by positivity
        simp only [coeffs, evalBound, BoundTerm.weight]
        calc (1 : ℚ) = 2 ^ 128 / 2 ^ 128 := (div_self hpos.ne').symm
          _ ≤ ((qH + qS : ℕ) : ℚ) / 2 ^ 128 := by gcongr
          _ = _ := by push_cast; ring
      exact_mod_cast hq

/-- Every clause except the structural keygen cap is satisfied by the forgeable scheme. -/
theorem almost_claim :
    CorrectOnSuccess cheat ∧ HasSigningFailureBound cheat signingFailureBits ∧
    HasAdaptiveSigningFailureBound cheat signingBudget (2 ^ securityFloor) signingFailureBits ∧
    HasAdaptiveSigningFailureBound cheat extendedSigningBudget (2 ^ extendedSecurityFloor)
      signingFailureBits ∧
    HasSignatureSize cheat 1 ∧ HasPublicKeySize cheat 32 ∧ HasVerificationBound cheat 1 ∧
    HasSignQueryBound cheat rawSignCap ∧ HasVerifyQueryBound cheat rawVerifyCap ∧
    HasKeygenSampleBound cheat sampleKeygenCap ∧ HasSignSampleBound cheat sampleSignCap ∧
    (∀ (A : Adversary) (qH qS : ℕ), qS ≤ extendedSigningBudget →
      HasHashQueryBound cheat A qH → HasSigningQueryBound A qS →
        sufAdvantage cheat A ≤ boundProbability coeffs (qH + qS) qS) ∧
    MeetsFloor coeffs signingBudget securityFloor ∧
    MeetsFloor coeffs extendedSigningBudget extendedSecurityFloor :=
  ⟨correct, signing_failure, adaptive_vacuous _ _ (by decide), adaptive_vacuous _ _ (by decide),
    sigma_size, public_key_size, fun _ _ _ => HasVerifyCost.pure _ _,
    fun _ _ => isQueryBoundP_pure _ _ _, fun _ _ _ => isQueryBoundP_pure _ _ _,
    keygen_samples, sign_samples,
    fun A qH qS _ hH _ => security_vacuous A qH qS hH,
    by norm_num [MeetsFloor, coeffs, evalBound, BoundTerm.weight, signingBudget, securityFloor],
    by norm_num [MeetsFloor, coeffs, evalBound, BoundTerm.weight, extendedSigningBudget,
      extendedSecurityFloor]⟩

/-- The structural keygen cap is the clause that rejects it. -/
theorem rejected : ¬ HasKeygenQueryBound cheat rawKeygenCap := by
  intro h
  have := deadBranch_forces (β := Bytes × Unit) (by simp) (fun _ => pure ([], ())) rawKeygenCap h
  exact absurd this (by decide)

theorem no_claim (sigma hverify : Nat) (coeffs : BoundCoeffs) :
    ¬ SchemeClaim cheat sigma hverify coeffs :=
  fun claim => rejected claim.keygen_queries

/-- Straight-line algorithms discharge the caps with the `pure` lemma. -/
private def straightLine : SigScheme where
  SecretKey := Unit
  keygen := pure ([], ())
  sign := fun _ _ => pure none
  verify := fun _ _ _ => pure false

example : HasKeygenQueryBound straightLine rawKeygenCap := isQueryBoundP_pure _ _ _
example : HasSignQueryBound straightLine rawSignCap := fun _ _ => isQueryBoundP_pure _ _ _
example : HasVerifyQueryBound straightLine rawVerifyCap := fun _ _ _ => isQueryBoundP_pure _ _ _
example : HasKeygenSampleBound straightLine sampleKeygenCap := isQueryBoundP_pure _ _ _
example : HasSignSampleBound straightLine sampleSignCap := fun _ _ => isQueryBoundP_pure _ _ _

end LeanSphincsTest.DeadBranch
