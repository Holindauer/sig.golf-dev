import LeanSphincsTest.Contract

/-! Comparator canary fixture `SmuggledAxiom`. Metric statements only: no signature
correctness or unforgeability claim is made or implied. -/

open LeanSphincs.Benchmark OracleComp

noncomputable def LeanSphincsTest.Submission.scheme : SigScheme :=
  { SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some [0]), verify := fun _ _ _ => pure true }

axiom LeanSphincsTest.Submission.smuggled :
    LeanSphincsTest.MetricClaim LeanSphincsTest.Submission.scheme 1 1 [⟨256, 0, 2, 0, 256⟩]

theorem LeanSphincsTest.candidate :
    LeanSphincsTest.MetricClaim LeanSphincsTest.Submission.scheme 1 1 [⟨256, 0, 2, 0, 256⟩] := by
  exact LeanSphincsTest.Submission.smuggled
