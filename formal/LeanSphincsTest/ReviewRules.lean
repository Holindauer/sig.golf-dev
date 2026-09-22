import LeanSphincs.Benchmark.Target

/-! Regression checks for the reviewed security rules, not accepted schemes. -/
open LeanSphincs.Benchmark OracleComp OracleSpec

private def smallKey (size : Nat) : SigScheme where
  SecretKey := Unit
  keygen := pure (List.replicate size 0, ())
  sign := fun _ _ => pure none
  verify := fun _ _ _ => pure false

example : HasPublicKeySize (smallKey 32) 32 := by
  intro keys hk
  have heq := OracleComp.eq_of_mem_support_pure (spec := OracleWorld)
    (List.replicate 32 (0 : UInt8), ()) hk
  subst keys
  simp

private theorem rejects_large_key : ¬ HasPublicKeySize (smallKey 33) 32 := by
  intro h
  have hb := h (List.replicate 33 0, ()) (by exact Set.mem_singleton _)
  norm_num at hb

example (sigma cost : Nat) (coeffs : BoundCoeffs) :
    ¬ SchemeClaim (smallKey 33) sigma cost coeffs := by
  intro h
  exact rejects_large_key h.public_key_size

/- Passing the normal lifetime does not automatically establish slow decay. -/
#guard MeetsFloor [⟨1, 0, 1, 3, 184⟩] signingBudget securityFloor
#guard ¬ MeetsFloor [⟨1, 0, 1, 3, 184⟩] extendedSigningBudget extendedSecurityFloor

/-- Equivalent bounds cannot acquire different meanings by dropping constants. -/
private def direct : BoundCoeffs := [⟨1, 0, 1, 0, 124⟩]
private def rescaled : BoundCoeffs := [⟨16, 0, 1, 0, 128⟩]
example (q : ℚ) (s : Nat) : evalBound direct q s = evalBound rescaled q s := by
  norm_num [direct, rescaled, evalBound, BoundTerm.weight]
#guard MeetsFloor direct signingBudget securityFloor
#guard MeetsFloor rescaled signingBudget securityFloor
#guard ¬ MeetsFloor (idealize direct) signingBudget 128
#guard MeetsFloor (idealize rescaled) signingBudget 128
