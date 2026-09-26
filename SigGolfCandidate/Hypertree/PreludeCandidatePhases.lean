import SigGolfCandidate.Hypertree.PreludeRun
import SigGolfCandidate.Hypertree.KeygenCache
import SigGolfCandidate.Hypertree.ExpandCopy
import SigGolfCandidate.Hypertree.VerifyCharged
namespace SigGolfCandidate.Hypertree.PreludeCandidate
open SigGolf OracleComp SignatureEncoding Signing.Prelude
set_option maxRecDepth 8192

theorem admitted : preludeSubmission.Admissible := by
  constructor
  · exact Hypertree.admitted.1
  · intro phase
    cases phase with
    | keygen => exact Hypertree.admitted.2 .keygen
    | sign => exact sign_valid
    | expand => exact Hypertree.admitted.2 .expand
    | verify => exact Hypertree.admitted.2 .verify

theorem keygen_eq (hash : Hash) (sk : SecretKey) :
    preludeSubmission.runWith hash .keygen sk = submission.runWith hash .keygen sk := rfl
 theorem expand_eq (hash : Hash) (input : Input submission.sizes .expand) :
    preludeSubmission.runWith hash .expand input = submission.runWith hash .expand input := rfl
 theorem verify_eq (hash : Hash) (input : Input submission.sizes .verify) :
    preludeSubmission.runWith hash .verify input = submission.runWith hash .verify input := rfl

theorem expand_exact (hash : Hash) (message : Message) (pk : PublicKey) (signature : Bytes signatureBytes) :
    preludeSubmission.runWith hash .expand (message,pk,signature)=⟨some signature,true,89733,0,0⟩ := by
  change submission.runWith hash .expand (message,pk,signature)=_
  have value := Expansion.run_identity hash (message,pk,signature)
  obtain ⟨finished,_,cycles,calls,blocks⟩ := Expansion.run_bound hash (message,pk,signature)
  cases h : submission.runWith hash .expand (message,pk,signature)
  simp only [h] at value finished cycles calls blocks
  cases value; cases finished; cases cycles; cases calls; cases blocks
  rfl


/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms admitted

/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.expand_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expand_exact
end SigGolfCandidate.Hypertree.PreludeCandidate
