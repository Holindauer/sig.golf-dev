import LeanSphincs.Benchmark.Bound

/-! Numerical regression fixtures from leanEthereum/leanVM-b PR #19,
head a1daec3b929d8963b4eee4f1e05985065a96de9d.
These certify arithmetic only, not a transport of the SPHINCS security proof. -/

open LeanSphincs.Benchmark

namespace LeanSphincsTest

/-- The public 126-bit slope, expressed against 128-bit digests. -/
def colleague126 : BoundCoeffs := [⟨4, 0, 1, 0, 128⟩]

/-- The refined endpoint's four terms: (10/3)q/2^128 + 19q/2^133
+ q/2^139 + q/2^216. Upstream uses this within its stated query range. -/
def colleagueRefined126 : BoundCoeffs :=
  [⟨10, 2, 1, 0, 128⟩, ⟨19, 0, 1, 0, 133⟩,
   ⟨1, 0, 1, 0, 139⟩, ⟨1, 0, 1, 0, 216⟩]

theorem colleague126_passes_mvp : MeetsFloor colleague126 (2^20) 124 := by
  norm_num [MeetsFloor, colleague126, evalBound, BoundTerm.weight]

theorem colleague126_floor : MeetsFloor colleague126 (2^24) 126 := by
  norm_num [MeetsFloor, colleague126, evalBound, BoundTerm.weight]

#guard bitSecurity colleague126 (2^24) = .finite 126
#guard bitSecurity colleagueRefined126 (2^24) = .finite 126
#guard bitSecurity (idealize colleague126) (2^24) = .finite 128
#guard ¬ MeetsFloor colleague126 (2^24) 127

end LeanSphincsTest
