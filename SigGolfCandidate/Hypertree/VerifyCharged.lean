import SigGolfCandidate.Hypertree.VerifyFunctional

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf
attribute [local instance] Classical.propDecidable

/-- Universal execution bound plus the organizer's witness-loading charge.
This is a verifier component theorem; the signing certificate is separate. -/
theorem run_refines_charged (hash : Hash) (pk : PublicKey) (message : Message)
    (witness : Bytes signatureBytes) :
    ∃ cycles calls blocks,
      cycles + witnessCycles signatureBytes ≤ 1633369 ∧
      calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      submission.runWith hash .verify (message, pk, witness) =
        ⟨if Reference.verify hash pk message (SignatureEncoding.decode witness).toReference
          then some () else none, true, cycles, calls, blocks⟩ := by
  obtain ⟨cycles, calls, blocks, bound, callsBound, blocksBound, run⟩ :=
    run_refines hash pk message witness
  have loading : witnessCycles signatureBytes = 468 := by decide
  exact ⟨cycles, calls, blocks, by rw [loading]; omega, callsBound, blocksBound, run⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.run_refines_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refines_charged
end SigGolfCandidate.Hypertree.Verifying
