import LeanSphincs.Benchmark.Target

/-! Comparator canary ONLY. This tests metric binding and the scheme hole,
and deliberately claims no signature correctness or unforgeability. -/

open LeanSphincs.Benchmark

namespace LeanSphincsTest

def MetricClaim (S : SigScheme) (sigma hverify : Nat) (coeffs : BoundCoeffs) : Prop :=
  HasSignatureSize S sigma ∧ HasVerificationBound S hverify ∧
    MeetsFloor coeffs (2^20) 124

end LeanSphincsTest
