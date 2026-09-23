import SigGolfCandidate.Hypertree.SecurityBytecodePrograms
import SigGolfCandidate.Hypertree.SecurityBytecodeCounts
import SigGolfCandidate.Hypertree.KeygenVerifyCountRun
import SigGolfCandidate.Hypertree.CandidateHonest

namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden SecurityVerifyCost SignatureEncoding
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def countHash {α : Type} (program : OracleComp HashSpec α) : OracleComp HashSpec (α×Nat) :=
  OracleComp.construct (fun value => pure (value,0))
    (fun input _ next => do
      let answer ← liftM (HashSpec.query input)
      let result ← next answer
      pure (result.1,result.2+1)) program

@[simp] theorem countHash_pure {α : Type} (value : α) : countHash (pure value)=pure (value,0) := rfl

theorem countHash_query_bind {α : Type} (input : Query) (next : BitVec 256 → OracleComp HashSpec α) :
    countHash (liftM (HashSpec.query input) >>= next) = (do
      let answer ← liftM (HashSpec.query input)
      let result ← countHash (next answer)
      pure (result.1,result.2+1)) := rfl

@[simp] theorem eval_countHash {α : Type} (hash : Hash) (program : OracleComp HashSpec α) :
    evalWithAnswerFn hash (countHash program)=(evalWithAnswerFn hash program,calls hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [countHash_query_bind,evalWithAnswerFn_bind,evalWithAnswerFn_pure,ih,calls_query_bind]
    rfl

def referenceSign (secretKey : SecretKey) (pk : PublicKey) (request : SigningRequest) :
    OracleComp HashSpec (Option (Bytes submission.sizes.signature)×Nat) :=
  countHash (SecurityExperiment.serialize <$> SecurityReference.signCompact secretKey pk request.message)

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
  change view (submission.runWith hash .keygen secretKey)=_
  rw [KeygenFunctional.run_exact]
  rfl

theorem sign_equivalent (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (request : SigningRequest)
    (validKey : Reference.keygen hash secretKey=pk) :
    evalWithAnswerFn hash (actualInterface.sign secretKey pk request)=
      evalWithAnswerFn hash (referenceInterface.sign secretKey pk request) := by
  obtain ⟨cycles,_,run⟩ := Signing.sign_run_refines hash secretKey pk request.cache request.message
  simp only [actualInterface,referenceInterface,referenceSign,eval_countHash,evalWithAnswerFn_map,
    SecurityReference.eval_signCompact,SecurityExperiment.serialize_valid _ (signCompact_valid _ _ _ _),
    calls_map,SecurityBytecodeCounts.calls_signCompact]
  change view (submission.runWith hash .sign (secretKey,pk,request.cache,request.message))=_
  rw [run,if_pos validKey]
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
    change (⟨(submission.runWith hash .verify (message,pk,witness)).value.isSome && _,
      transcript.hashCalls+(submission.runWith hash .verify (message,pk,witness)).hashCalls⟩ : AttackResult)=_
    rw [run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]
  | signature message signature =>
    obtain ⟨cycles,vcalls,blocks,_,_,_,run⟩ := Verifying.run_refines hash pk message signature
    have counted := KeygenVerifyCount.run_calls_reference hash pk message signature
    rw [run] at counted
    simp only [actualInterface,referenceInterface,Submission.checkForgery,referenceCheck,
      evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_countHash]
    have ex : evalWithAnswerFn hash (submission.run .expand (message,pk,signature)) =
        ⟨some signature,true,85221,0,0⟩ := Candidate.expand_exact hash message pk signature
    simp only [ex,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    change (⟨(submission.runWith hash .verify (message,pk,signature)).value.isSome && _,
      transcript.hashCalls+0+(submission.runWith hash .verify (message,pk,signature)).hashCalls⟩ : AttackResult)=_
    rw [run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]

end SigGolfCandidate.Hypertree.SecurityBytecode
