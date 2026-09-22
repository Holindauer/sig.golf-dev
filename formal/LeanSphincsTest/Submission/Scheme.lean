import LeanSphincsTest.Contract

noncomputable def LeanSphincsTest.Submission.scheme : LeanSphincs.Benchmark.SigScheme :=
  { SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some [0]), verify := fun _ _ _ => pure false }
