import SigGolfCandidate.Hypertree.PreludeSecuritySign
import SigGolfCandidate.Hypertree.SecurityBytecodePrograms
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode SecurityVerifyCost SignatureEncoding Signing.Prelude
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


/-- Existing reference signing queries, with explicit machine derivation overhead charged. -/
def referenceSign (secretKey : SecretKey) (pk : PublicKey) (request : SigningRequest) :
    OracleComp HashSpec (Option (Bytes submission.sizes.signature) × Nat) := do
  let result ← countHash (SecurityExperiment.serialize <$> SecurityReference.signCompact secretKey pk request.message)
  pure (result.1,result.2+739)

def actualInterface : Interface where
  keygen secretKey := view <$> preludeSubmission.run .keygen secretKey
  sign secretKey _ request := view <$> preludeSubmission.signingOracle secretKey request
  check := preludeSubmission.checkForgery

theorem sign_equivalent (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (request : SigningRequest)
    (validKey : Reference.keygen hash secretKey=pk) :
    evalWithAnswerFn hash (actualInterface.sign secretKey pk request) =
      evalWithAnswerFn hash (referenceSign secretKey pk request) := by
  obtain ⟨cycles,_,run⟩ := sign_run_refines hash secretKey request.cache request.message
  simp only [actualInterface,referenceSign,evalWithAnswerFn_bind,evalWithAnswerFn_pure,
    eval_countHash,evalWithAnswerFn_map,SecurityReference.eval_signCompact,
    SecurityExperiment.serialize_valid _ (signCompact_valid _ _ _ _),
    calls_map,SecurityBytecodeCounts.calls_signCompact]
  change view (preludeSubmission.runWith hash .sign (secretKey,request.cache,request.message)) = _
  rw [run,validKey]
  rfl
theorem actual_interact (adversary : Adversary preludeSubmission.sizes) (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript preludeSubmission.sizes) :
    interactWith actualInterface adversary secretKey pk rounds state transcript=
      preludeSubmission.interact adversary secretKey pk rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
    simp only [interactWith,Submission.interact]
    cases h : adversary.step state <;> simp only [h] at *
    case submit candidate => rfl
    case hash input resume => simp only [ih]
    case sign request resume =>
      split
      · change ((view <$> preludeSubmission.signingOracle secretKey request).liftComp World >>= _) = _
        simp only [OracleComp.liftComp_map,map_eq_bind_pure_comp,OracleComp.liftComp_bind,OracleComp.liftComp_pure,bind_assoc,pure_bind,Function.comp_def]
        apply bind_congr
        intro result
        change interactWith actualInterface adversary secretKey pk rounds (resume result.value)
          (recordView transcript request.message (view result)) = _
        rw [record_view]
        exact ih _ _
      · rfl
    case sample n resume => simp only [ih]
    case step next => exact ih next transcript
theorem actual_experiment (adversary : Adversary preludeSubmission.sizes) (rounds : Nat) :
    experimentWith actualInterface adversary rounds=preludeSubmission.securityExperiment adversary rounds := by
  unfold experimentWith Submission.securityExperiment
  congr 1
  apply bind_congr
  intro secretKey
  simp only [actualInterface,OracleComp.liftComp_map,bind_map_left,view]
  apply bind_congr
  intro result
  cases result.value with
  | none => rfl
  | some pair =>
    rcases pair with ⟨pk,cache⟩
    exact actual_interact adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=result.hashCalls}

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.sign_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_equivalent

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.actual_experiment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_experiment

end SigGolfCandidate.Hypertree.PreludeSecurity
