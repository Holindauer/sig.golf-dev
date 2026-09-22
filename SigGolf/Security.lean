import SigGolf.Programs

namespace SigGolf
open OracleComp OracleSpec

structure SigningRequest where
  message : Message
  cache : Cache

/-- The attacker supplies only the message and cache. All signing work, including any internal search, is charged. -/
def Submission.signingOracle (submission : Submission) (seed : Seed) (pk : PublicKey)
    (request : SigningRequest) : OracleComp HashSpec (RunResult (Bytes submission.sizes.signature)) :=
  submission.run .sign (seed, pk, request.cache, request.message)

inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)

/-- A classical interactive strategy. Only oracle responses and private coins reveal new information. Local computation is unrestricted. -/
inductive Action (sizes : Sizes) (state : Type) where
  | submit (candidate : Forgery sizes)
  | hash (input : Query) (resume : BitVec 256 → state)
  | sign (request : SigningRequest) (resume : Option (Bytes sizes.signature) → state)
  | sample (n : Nat) (resume : Fin (n + 1) → state)
  | step (next : state)

structure Adversary (sizes : Sizes) where
  State : Type
  initial : PublicKey → Cache → State
  step : State → Action sizes State

structure Transcript (sizes : Sizes) where
  signed : List (Message × Bytes sizes.signature) := []
  signingRequests : Nat := 0
  hashCalls : Nat := 0

/-- Failed signing requests consume a slot and hash calls but add no replay entry. -/
def Transcript.record {sizes : Sizes} (transcript : Transcript sizes) (message : Message)
    (result : RunResult (Bytes sizes.signature)) : Transcript sizes :=
  { signed := match result.value with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1
    hashCalls := transcript.hashCalls + result.hashCalls }

structure AttackResult where
  won : Bool
  hashCalls : Nat
  deriving DecidableEq, Repr

def Transcript.freshMessage {sizes : Sizes} (transcript : Transcript sizes) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)

def Transcript.freshSignature {sizes : Sizes} (transcript : Transcript sizes)
    (message : Message) (signature : Bytes sizes.signature) : Bool :=
  !transcript.signed.contains (message, signature)

/-- The final checker uses the original public key. All its hash calls are charged, including failed expansion or verification. -/
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (transcript : Transcript submission.sizes) : Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshMessage message,
        transcript.hashCalls + verify.hashCalls⟩
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let calls := transcript.hashCalls + expand.hashCalls
      let some witness := expand.value | return ⟨false, calls⟩
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshSignature message signature,
        calls + verify.hashCalls⟩

/-- Observation depth bounds only the prefix being observed, not the attacker. Security is required at every depth. A strategy can run indefinitely but wins only by making its single final submission. -/
def Submission.interact (submission : Submission) (adversary : Adversary submission.sizes)
    (seed : Seed) (pk : PublicKey) : Nat → adversary.State → Transcript submission.sizes →
      OracleComp World AttackResult
  | 0, _, transcript => pure ⟨false, transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => liftM (submission.checkForgery pk transcript candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          submission.interact adversary seed pk rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← liftM (submission.signingOracle seed pk request)
            submission.interact adversary seed pk rounds (resume result.value)
              (transcript.record request.message result)
          else return ⟨false, transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          submission.interact adversary seed pk rounds (resume answer) transcript
      | .step next => submission.interact adversary seed pk rounds next transcript

noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) (rounds : Nat) : ProbComp AttackResult :=
  withRandomness do
    let seed ← liftM sampleSeed
    let keygen ← liftM (submission.run .keygen seed)
    let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
    submission.interact adversary seed pk rounds (adversary.initial pk cache)
      { hashCalls := keygen.hashCalls }

/-- Both final-submission forms, every total-call budget, and every finite prefix of every adaptive strategy. There is no bound on attacker computation or private randomness. -/
def Submission.Secure (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds Q : Nat), 1 ≤ Q →
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q |
      submission.securityExperiment adversary rounds] ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

end SigGolf
