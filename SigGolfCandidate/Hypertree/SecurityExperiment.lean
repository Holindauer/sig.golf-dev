import SigGolfCandidate.Hypertree.SecurityForgery
import SigGolfCandidate.Hypertree.SecurityIdealSign
import SigGolfCandidate.Hypertree.SecurityQueryCosts

namespace SigGolfCandidate.Hypertree.SecurityExperiment
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityDerivation SecurityGameHop

/-- A compact serialization with a total fallback. The signer validity theorem
shows that the fallback cannot occur for either real or ideal signing. -/
def serialize (signature : Compact) : Option (Bytes signatureBytes) :=
  if valid : signature.upper.length = 159 then some (signature.wire valid) else none

@[simp] theorem serialize_valid (signature : Compact) (valid : signature.Valid) :
    serialize signature = some (signature.wire valid) := by simp [serialize, show signature.upper.length = 159 from valid]

def signWire (pk : PublicKey) (message : Message) : OracleComp SplitWorld (Option (Bytes signatureBytes)) :=
  serialize <$> SecurityIdealSign.signCompact pk message

@[simp] theorem simulate_signWire (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    simulateQ (realImplementation secretKey) (signWire pk message) =
      serialize <$> SecurityReference.signCompact secretKey pk message := by
  simp [signWire, SecurityIdealSign.simulate_signCompact]

@[simp] theorem eval_signWire (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    evalWithAnswerFn hash (simulateQ (realImplementation secretKey) (signWire pk message)) =
      some ((SignatureEncoding.signCompact hash secretKey pk message).wire (signCompact_valid hash secretKey pk message)) := by
  simp [simulate_signWire, SecurityReference.eval_signCompact, signCompact_valid]

/-- Keep the accepted forgery and raw organizer transcript for the deterministic
extraction boundary. No resource count is fabricated inside this record. -/
structure Result where
  won : Bool
  candidate : Option (Message × Compact)
  transcript : Transcript submission.sizes

def check (pk : PublicKey) (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → OracleComp GameWorld Result
  | .witness message witness => do
      let signature := decode witness
      let accepted ← (SecurityVerify.verifyCompact pk message signature).liftComp GameWorld
      return ⟨accepted && transcript.freshMessage message, some (message, signature), transcript⟩
  | .signature message wire => do
      let signature := decode wire
      let accepted ← (SecurityVerify.verifyCompact pk message signature).liftComp GameWorld
      return ⟨accepted && transcript.freshSignature message wire, some (message, signature), transcript⟩

/-- The real organizer strategy interface: cache-supplied signing requests, private
coins, local steps, both forgery forms, and the lifetime counter are retained. -/
def interact (adversary : Adversary submission.sizes) (pk : PublicKey) :
    Nat → adversary.State → Transcript submission.sizes → OracleComp GameWorld Result
  | 0, _, transcript => pure ⟨false, none, transcript⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => check pk transcript candidate
      | .hash input resume => do
          let answer ← liftM (GameWorld.query (.inr (.inr input)))
          interact adversary pk rounds (resume answer) transcript
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← (signWire pk request.message).liftComp GameWorld
            let next : Transcript submission.sizes :=
              { transcript with
                signed := match result with
                  | none => transcript.signed
                  | some signature => (request.message, signature) :: transcript.signed
                signingRequests := transcript.signingRequests + 1 }
            interact adversary pk rounds (resume result) next
          else return ⟨false, none, transcript⟩
      | .sample n resume => do
          let answer ← liftM (GameWorld.query (.inl n))
          interact adversary pk rounds (resume answer) transcript
      | .step next => interact adversary pk rounds next transcript

/-- `publicCache` is explicit until key-generation bytecode refinement establishes
its exact fixed value. It is passed to the attacker exactly once, as in the organizer. -/
def program (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds : Nat) :
    OracleComp GameWorld Result := do
  let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
  interact adversary pk rounds (adversary.initial pk publicCache) {}

/-- Every H call, including keygen, honest signing, and final verification, is
counted externally by the already-checked query-cost semantics. -/
noncomputable def idealExperiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) : ProbComp AttackResult :=
  (fun result => ⟨result.1.won, result.2⟩) <$>
    (simulateQ idealGameOracle (SecurityBudget.counted (program publicCache adversary rounds))).run' (∅, ∅)

noncomputable def realExperiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) : ProbComp AttackResult := do
  let secretKey ← sampleSecretKey
  (fun result => ⟨result.1.won, result.2⟩) <$>
    (simulateQ (realGameOracle secretKey) (SecurityBudget.counted (program publicCache adversary rounds))).run' ∅

/-- The secret key-erasure theorem now applies to the concrete organizer-style reference
experiment, rather than a sampler with no adversary/signing interface. -/
theorem realExperiment_le_ideal_add_secretKey (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      realExperiment publicCache adversary rounds] ≤
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      idealExperiment publicCache adversary rounds] + (budget : ENNReal) / 2 ^ 128 := by
  have h := SecurityBudget.prob_counted_real_le_ideal_add_secretKey
    (program publicCache adversary rounds) budget (fun result => result.won = true)
  simpa only [realExperiment, idealExperiment, probEvent_bind_eq_tsum,
    probEvent_map, Function.comp_def] using h

end SigGolfCandidate.Hypertree.SecurityExperiment
