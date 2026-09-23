import SigGolfCandidate.Hypertree.CandidateFields
import SigGolfCandidate.Hypertree.SecurityMonitorRealTransfer

namespace SigGolfCandidate.Hypertree.Candidate
open SigGolf OracleComp

/-- Security of the actual four RISC-V images against every adaptive adversary, at every total hash-call budget. -/
theorem security : submission.Secure := by
  intro adversary rounds budget _
  rw [SecurityActualCutoff.actual_probability]
  exact SecurityMonitorRealTransfer.real_bound KeygenFunctional.zeroCache adversary rounds budget

/-- The complete organizer certificate for the exact submitted images and claimed verification cycles. -/
theorem certificate : SigGolf.Certificate submission 5883520 :=
  certificate_of_secure security

/-- info: 'SigGolfCandidate.Hypertree.Candidate.security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms security

/-- info: 'SigGolfCandidate.Hypertree.Candidate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end SigGolfCandidate.Hypertree.Candidate
