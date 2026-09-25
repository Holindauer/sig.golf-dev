import SigGolfCandidate.Hypertree.SecurityBytecodeCache
import SigGolfCandidate.Hypertree.SecurityVerifyCost

namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden SecurityVerifyCost
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def view {α : Type} (result : RunResult α) : Option α × Nat := (result.value,result.hashCalls)

def recordView (transcript : Transcript submission.sizes) (message : Message)
    (result : Option (Bytes submission.sizes.signature) × Nat) : Transcript submission.sizes :=
  { signed := match result.1 with
      | none => transcript.signed
      | some signature => (message,signature)::transcript.signed
    signingRequests := transcript.signingRequests+1
    hashCalls := transcript.hashCalls+result.2 }

theorem record_view (transcript : Transcript submission.sizes) (message : Message)
    (result : RunResult (Bytes submission.sizes.signature)) : recordView transcript message (view result)=transcript.record message result := by
  cases result with
  | mk value finished cycles calls blocks =>
    cases value <;> rfl

/-- Every value observed by the organizer security experiment, excluding unobserved cycle fields. -/
structure Interface where
  keygen : SecretKey → OracleComp HashSpec (Option (PublicKey×Cache) × Nat)
  sign : SecretKey → PublicKey → SigningRequest → OracleComp HashSpec (Option (Bytes submission.sizes.signature) × Nat)
  check : PublicKey → Transcript submission.sizes → Forgery submission.sizes → OracleComp HashSpec AttackResult

def actualInterface : Interface where
  keygen secretKey := view <$> submission.run .keygen secretKey
  sign secretKey pk request := view <$> submission.signingOracle secretKey request
  check := submission.checkForgery

def interactWith (scheme : Interface) (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) : Nat → adversary.State → Transcript submission.sizes → OracleComp World AttackResult
  | 0,_,transcript => pure ⟨false,transcript.hashCalls⟩
  | rounds+1,state,transcript =>
      match adversary.step state with
      | .submit candidate => (scheme.check pk transcript candidate).liftComp World
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          interactWith scheme adversary secretKey pk rounds (resume answer) {transcript with hashCalls:=transcript.hashCalls+1}
      | .sign request resume => do
          if transcript.signingRequests<LIFETIME then
            let result ← (scheme.sign secretKey pk request).liftComp World
            interactWith scheme adversary secretKey pk rounds (resume result.1) (recordView transcript request.message result)
          else pure ⟨false,transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          interactWith scheme adversary secretKey pk rounds (resume answer) transcript
      | .step next => interactWith scheme adversary secretKey pk rounds next transcript

noncomputable def experimentWith (scheme : Interface) (adversary : Adversary submission.sizes) (rounds : Nat) : ProbComp AttackResult :=
  withRandomness do
    let secretKey ← liftM sampleSecretKey
    let keygen ← (scheme.keygen secretKey).liftComp World
    let some (pk,cache) := keygen.1 | pure ⟨false,keygen.2⟩
    interactWith scheme adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=keygen.2}

theorem actual_interact (adversary : Adversary submission.sizes) (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) :
    interactWith actualInterface adversary secretKey pk rounds state transcript=
      submission.interact adversary secretKey pk rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
    simp only [interactWith,Submission.interact]
    cases h : adversary.step state <;> simp only [h] at *
    case submit candidate => rfl
    case hash input resume => simp only [ih]
    case sign request resume =>
      split
      · change ((view <$> submission.signingOracle secretKey request).liftComp World >>= _) = _
        rw [OracleComp.liftComp_map,bind_map_left]
        apply bind_congr
        intro result
        change interactWith actualInterface adversary secretKey pk rounds (resume result.value)
          (recordView transcript request.message (view result)) = _
        rw [record_view]
        exact ih _ _
      · rfl
    case sample n resume => simp only [ih]
    case step next => exact ih next transcript
theorem actual_experiment (adversary : Adversary submission.sizes) (rounds : Nat) :
    experimentWith actualInterface adversary rounds=submission.securityExperiment adversary rounds := by
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

end SigGolfCandidate.Hypertree.SecurityBytecode
