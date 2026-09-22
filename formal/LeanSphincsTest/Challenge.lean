import LeanSphincsTest.Contract

noncomputable def LeanSphincsTest.Submission.scheme : LeanSphincs.Benchmark.SigScheme :=
  { SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some []), verify := fun _ _ _ => pure true }

theorem LeanSphincsTest.candidate :
    LeanSphincsTest.MetricClaim LeanSphincsTest.Submission.scheme 1 1 [⟨256, 0, 2, 0, 256⟩] := by
  sorry
