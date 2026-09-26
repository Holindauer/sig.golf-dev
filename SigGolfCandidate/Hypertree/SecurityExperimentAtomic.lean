import SigGolfCandidate.Hypertree.SecurityAtomicCountsSign
import SigGolfCandidate.Hypertree.SecurityAtomicCutoffRun

namespace SigGolfCandidate.Hypertree.SecurityExperimentAtomic
open SigGolf OracleComp OracleSpec SecurityDerivation SecurityGameHop SecuritySeparation
  SecurityBudget SecurityExperiment SecurityAtomicCutoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The exact transcript update of the reference signing action, including a
failed response. The external counted/cutoff semantics charges the hash work. -/
def afterSign (transcript : Transcript submission.sizes) (message : Message)
    (response : Option (Bytes submission.sizes.signature)) : Transcript submission.sizes :=
  { transcript with
    signed := match response with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1 }

def signContinuation (adversary : Adversary submission.sizes) (pk : PublicKey) (rounds : Nat)
    (transcript : Transcript submission.sizes) (request : SigningRequest)
    (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (response : Option (Bytes submission.sizes.signature)) : OracleComp GameWorld Result :=
  interact adversary pk rounds (resume response) (afterSign transcript request.message response)

/-- Key generation is the actual first block of the reference experiment. -/
theorem program_cutoff_enough (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (enough : 739 ≤ budget) :
    cutoff (program publicCache adversary rounds) budget = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      cutoff (interact adversary pk rounds (adversary.initial pk publicCache) {}) (budget - 739)) :=
  SecurityAtomicCounts.keygen.bind_enough _ budget enough

/-- Exact terminal-output scheduling rule for the actual experiment's keygen,
under the actual ideal game oracle and an arbitrary current cache. -/
theorem program_atomic_run (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) :
    𝒮[(simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run' cache] =
      if 739 ≤ budget then
        𝒮[(simulateQ idealGameOracle (do
          let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
          cutoff (interact adversary pk rounds (adversary.initial pk publicCache) {}) (budget - 739))).run' cache]
      else 𝒮[(pure (none : Option Result) : ProbComp (Option Result))] :=
  SecurityAtomicCounts.keygen.ideal_atomic_run _ cache budget

/-- Sufficient keygen budget retains its complete resulting oracle state before
entering the adversary with precisely the remaining budget. -/
theorem program_run_enough (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) (enough : 739 ≤ budget) :
    (simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run cache =
      ((simulateQ idealGameOracle (SecurityIdealKeygen.keygen.liftComp GameWorld)).run cache >>= fun first =>
        (simulateQ idealGameOracle (cutoff
          (interact adversary first.1 rounds (adversary.initial first.1 publicCache) {}) (budget - 739))).run first.2) :=
  SecurityAtomicCounts.keygen.run_bind_enough idealGameOracle _ cache budget enough

/-- An unaffordable keygen has no completed experiment output. -/
theorem program_run_insufficient (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) (short : budget < 739) :
    𝒮[(simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run' cache] =
      𝒮[(pure (none : Option Result) : ProbComp (Option Result))] := by
  rw [program_atomic_run, if_neg (by omega)]

/-- Unfold only the actual signing action; the 117508-query body stays opaque. -/
theorem interact_sign (adversary : Adversary submission.sizes) (pk : PublicKey) (rounds : Nat)
    (state : adversary.State) (transcript : Transcript submission.sizes) (request : SigningRequest)
    (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) :
    interact adversary pk (rounds + 1) state transcript =
      ((signWire pk request.message).liftComp GameWorld >>=
        signContinuation adversary pk rounds transcript request resume) := by
  simp only [interact, action, if_pos allowed]
  rfl

/-- The exact signing response resumes the actual adversary and updates exactly
one signing slot before execution continues with the remaining budget. -/
theorem interact_sign_cutoff_enough (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (enough : 117508 ≤ budget) :
    cutoff (interact adversary pk (rounds + 1) state transcript) budget = (do
      let response ← (signWire pk request.message).liftComp GameWorld
      cutoff (signContinuation adversary pk rounds transcript request resume response) (budget - 117508)) := by
  rw [interact_sign adversary pk rounds state transcript request resume action allowed]
  exact (SecurityAtomicCounts.signWire pk request.message).bind_enough _ budget enough

/-- Stateful signing-block decomposition under the actual ideal oracle. -/
theorem interact_sign_run_enough (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (enough : 117508 ≤ budget) :
    (simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run cache =
      ((simulateQ idealGameOracle ((signWire pk request.message).liftComp GameWorld)).run cache >>= fun first =>
        (simulateQ idealGameOracle (cutoff
          (signContinuation adversary pk rounds transcript request resume first.1) (budget - 117508))).run first.2) := by
  rw [interact_sign adversary pk rounds state transcript request resume action allowed]
  exact (SecurityAtomicCounts.signWire pk request.message).run_bind_enough idealGameOracle _ cache budget enough

/-- Signing at the lifetime limit returns the reference failure result without
entering the signing block, for every remaining query budget. -/
theorem interact_sign_lifetime (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (exhausted : LIFETIME ≤ transcript.signingRequests) :
    cutoff (interact adversary pk (rounds + 1) state transcript) budget =
      pure (some (⟨false, none, transcript⟩ : Result)) := by
  simp only [interact, action, if_neg (by omega : ¬transcript.signingRequests < LIFETIME), cutoff_pure]

/-- Complete actual signing-action scheduling, with both lifetime and hash-call
gates. No extra no-failure or fixed-H assumptions are required. -/
theorem interact_sign_atomic_run (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume) :
    𝒮[(simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run' cache] =
      if transcript.signingRequests < LIFETIME then
        if 117508 ≤ budget then
          𝒮[(simulateQ idealGameOracle (do
            let response ← (signWire pk request.message).liftComp GameWorld
            cutoff (signContinuation adversary pk rounds transcript request resume response) (budget - 117508))).run' cache]
        else 𝒮[(pure (none : Option Result) : ProbComp (Option Result))]
      else 𝒮[(pure (some (⟨false, none, transcript⟩ : Result)) : ProbComp (Option Result))] := by
  by_cases allowed : transcript.signingRequests < LIFETIME
  · rw [if_pos allowed, interact_sign adversary pk rounds state transcript request resume action allowed]
    exact (SecurityAtomicCounts.signWire pk request.message).ideal_atomic_run _ cache budget
  · rw [if_neg allowed, interact_sign_lifetime adversary pk rounds budget state transcript request resume action (by omega)]
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]

/-- Insufficient signing budget aborts before any completed response is delivered
to the adversary, even though the attempted prefix may have touched hidden cache state. -/
theorem interact_sign_run_insufficient (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (short : budget < 117508) :
    𝒮[(simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run' cache] =
      𝒮[(pure (none : Option Result) : ProbComp (Option Result))] := by
  rw [interact_sign_atomic_run adversary pk rounds budget state transcript request resume cache action,
    if_pos allowed, if_neg (by omega)]

end SigGolfCandidate.Hypertree.SecurityExperimentAtomic
