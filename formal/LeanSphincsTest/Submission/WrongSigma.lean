import LeanSphincsTest.Contract

/-! Comparator canary fixture `WrongSigma`. Metric statements only: no signature
correctness or unforgeability claim is made or implied. -/

open LeanSphincs.Benchmark OracleComp

noncomputable def LeanSphincsTest.Submission.scheme : SigScheme :=
  { SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some [0, 0]), verify := fun _ _ _ => pure true }

theorem LeanSphincsTest.candidate :
    LeanSphincsTest.MetricClaim LeanSphincsTest.Submission.scheme 2 1 [⟨256, 0, 2, 0, 256⟩] := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ signature h
    have h' := OracleComp.eq_of_mem_support_pure _ h
    simp only [Option.some.injEq] at h'
    subst h'
    rfl
  · intro _ _ _
    exact HasVerifyCost.pure _ _
  · norm_num [MeetsFloor, evalBound, BoundTerm.weight]
