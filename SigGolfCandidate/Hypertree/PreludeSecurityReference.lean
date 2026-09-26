import SigGolfCandidate.Hypertree.PreludeSecurityInterface
import SigGolfCandidate.Hypertree.PreludeCandidatePhases
import SigGolfCandidate.Hypertree.KeygenVerifyCountRun
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode SecurityCache SecurityGraphHidden SecurityVerifyCost SignatureEncoding Signing.Prelude
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
def referenceKeygen (secretKey : SecretKey) : OracleComp HashSpec (Option (PublicKey×Cache)×Nat) := do
  let result ← countHash (SecurityReference.keygen secretKey)
  pure (some (result.1,KeygenFunctional.zeroCache),result.2)

def referenceCheck (pk : PublicKey) (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let result ← countHash (SecurityVerify.verifyCompact pk message (decode witness))
      pure ⟨result.1 && transcript.freshMessage message,transcript.hashCalls+result.2⟩
  | .signature message signature => do
      let result ← countHash (SecurityVerify.verifyCompact pk message (decode signature))
      pure ⟨result.1 && transcript.freshSignature message signature,transcript.hashCalls+result.2⟩

def referenceInterface : Interface where
  keygen := referenceKeygen
  sign := referenceSign
  check := referenceCheck

theorem keygen_equivalent (hash : Hash) (secretKey : SecretKey) :
    evalWithAnswerFn hash (actualInterface.keygen secretKey)=evalWithAnswerFn hash (referenceInterface.keygen secretKey) := by
  simp only [actualInterface,referenceInterface,referenceKeygen,evalWithAnswerFn_map,evalWithAnswerFn_bind,
    evalWithAnswerFn_pure,eval_countHash,SecurityReference.eval_keygen,SecurityBytecodeCounts.calls_keygen]
  change view (preludeSubmission.runWith hash .keygen secretKey)=_
  rw [PreludeCandidate.keygen_eq,KeygenFunctional.run_exact]
  rfl

theorem check_equivalent (hash : Hash) (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) :
    evalWithAnswerFn hash (actualInterface.check pk transcript forgery)=
      evalWithAnswerFn hash (referenceInterface.check pk transcript forgery) := by
  classical
  cases forgery with
  | witness message witness =>
    obtain ⟨cycles,vcalls,blocks,_,_,_,run⟩ := Verifying.run_refines hash pk message witness
    have counted := KeygenVerifyCount.run_calls_reference hash pk message witness
    rw [run] at counted
    simp only [actualInterface,referenceInterface,Submission.checkForgery,referenceCheck,
      evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_countHash]
    change (⟨(preludeSubmission.runWith hash .verify (message,pk,witness)).value.isSome && _,
      transcript.hashCalls+(preludeSubmission.runWith hash .verify (message,pk,witness)).hashCalls⟩ : AttackResult)=_
    rw [PreludeCandidate.verify_eq,run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]
  | signature message signature =>
    obtain ⟨cycles,vcalls,blocks,_,_,_,run⟩ := Verifying.run_refines hash pk message signature
    have counted := KeygenVerifyCount.run_calls_reference hash pk message signature
    rw [run] at counted
    simp only [actualInterface,referenceInterface,Submission.checkForgery,referenceCheck,
      evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_countHash]
    have ex : evalWithAnswerFn hash (preludeSubmission.run .expand (message,pk,signature)) =
        ⟨some signature,true,89733,0,0⟩ := PreludeCandidate.expand_exact hash message pk signature
    simp only [ex,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    change (⟨(preludeSubmission.runWith hash .verify (message,pk,signature)).value.isSome && _,
      transcript.hashCalls+0+(preludeSubmission.runWith hash .verify (message,pk,signature)).hashCalls⟩ : AttackResult)=_
    rw [PreludeCandidate.verify_eq,run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.keygen_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_equivalent
/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.check_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_equivalent
end SigGolfCandidate.Hypertree.PreludeSecurity
