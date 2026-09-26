import SigGolfCandidate.Hypertree.PreludeCandidateFields
import SigGolfCandidate.Hypertree.PreludeMonitorRealTransfer
namespace SigGolfCandidate.Hypertree.PreludeCandidate
open SigGolf OracleComp Signing.Prelude
set_option backward.isDefEq.respectTransparency false

/-- Universal security of the current three-input signer, including repeated key derivation. -/
theorem security : preludeSubmission.Secure := by
  intro adversary rounds budget _
  change Adversary submission.sizes at adversary
  apply (PreludeSecurity.actual_probability_le_base adversary rounds budget).trans
  rw [← PreludeReferenceAdapter.reference_experiment,
    ← PreludeReferenceCutoff.reference_probability]
  exact PreludeMonitorRealTransfer.real_bound KeygenFunctional.zeroCache adversary rounds budget

theorem certificate : Certificate preludeSubmission 1633369 :=
  certificate_of_secure security

/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms security
/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certificate
end SigGolfCandidate.Hypertree.PreludeCandidate
