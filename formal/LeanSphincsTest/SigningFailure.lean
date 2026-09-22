import LeanSphincs.Benchmark.Target

/-! Regression fixtures for the independent correctness and availability gates.
These toy schemes make no unforgeability claim. -/

open LeanSphincs.Benchmark OracleComp OracleSpec ENNReal

namespace LeanSphincsTest.SigningFailure

def toy (result : Option Bytes) (accept : Bool) : SigScheme where
  SecretKey := Unit
  keygen := pure ([], ())
  sign := fun _ _ => pure result
  verify := fun _ _ _ => pure accept

example : CorrectOnSuccess (toy none false) := by
  simp [CorrectOnSuccess, correctnessExperiment, toy, runROM]

theorem rejects_always_failing :
    ¬ HasSigningFailureBound (toy none false) signingFailureBits := by
  simp [HasSigningFailureBound, signingFailureExperiment, toy, runROM]
  norm_num [signingFailureBits]

example (sigma hverify : Nat) (coeffs : BoundCoeffs) :
    ¬ SchemeClaim (toy none false) sigma hverify coeffs :=
  fun claim => rejects_always_failing claim.signing_failure

example : CorrectOnSuccess (toy (some [0]) true) := by
  simp [CorrectOnSuccess, correctnessExperiment, toy, runROM]

example : HasSigningFailureBound (toy (some [0]) true) 256 := by
  simp [HasSigningFailureBound, signingFailureExperiment, toy, runROM]

example : ¬ CorrectOnSuccess (toy (some [0]) false) := by
  simp [CorrectOnSuccess, correctnessExperiment, toy, runROM]

example (S : SigScheme) (h : HasSigningFailureBound S 256) :
    HasSigningFailureBound S signingFailureBits :=
  h.mono (by decide)

def oneRequest : Adversary where
  main := fun _ => do
    let _ ← (OracleWorld + SigningSpec).query (.inr 0)
    return ⟨0, []⟩

/-- Even a request whose response is ignored (possibly `none`) needs budget. -/
example : HasSigningQueryBound oneRequest 1 := by
  intro pk
  exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

example : ¬ HasSigningQueryBound oneRequest 0 := by
  intro h
  exact (h []).1.elim (fun hnp => hnp rfl) (Nat.not_lt_zero _)

/-- Failure is not an empty-byte signature and cannot exclude a forgery as replay. -/
example (message : Message) (signature : Bytes) :
    ¬ IsReplay [⟨message, none⟩] ⟨message, signature⟩ := by
  simp [IsReplay]

end LeanSphincsTest.SigningFailure
