import SphincsSecurity.Proof.Security126Completion

/- Run with PR #19's formal/sphincs Lake environment. This checks the exact
completed 126-bit dependency path without importing the ongoing 127-bit work. -/

example : SphincsSecurity.SphincsSecurity126Statement :=
  SphincsSecurity.Concrete.OtsProbeSimulation.security126_of_completed_native_boundary

/-- info: 'SphincsSecurity.Concrete.OtsProbeSimulation.security126_of_completed_native_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.OtsProbeSimulation.security126_of_completed_native_boundary
