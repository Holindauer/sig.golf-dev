import SigGolfCandidate.Hypertree.PreludeSecurityExperiment
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode SignatureEncoding
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def baseReferenceSign (secretKey : SecretKey) (pk : PublicKey) (request : SigningRequest) :=
  countHash (SecurityExperiment.serialize <$> SecurityReference.signCompact secretKey pk request.message)

def baseReferenceInterface : Interface where
  keygen := referenceKeygen
  sign := baseReferenceSign
  check := referenceCheck

def addTranscriptCalls (t : Transcript submission.sizes) (extra : Nat) : Transcript submission.sizes :=
  {t with hashCalls := t.hashCalls+extra}

def addResultCalls (r : AttackResult) (extra : Nat) : AttackResult :=
  {r with hashCalls := r.hashCalls+extra}

theorem signing_charge (sk : SecretKey) (pk : PublicKey) (request : SigningRequest) :
    referenceSign sk pk request = (fun r => (r.1,r.2+739)) <$> baseReferenceSign sk pk request := by
  simp only [referenceSign,baseReferenceSign,map_eq_bind_pure_comp,Function.comp_def]

theorem record_charge (t : Transcript submission.sizes) (message : Message)
    (r : Option (Bytes signatureBytes) × Nat) (extra : Nat) :
    recordView (addTranscriptCalls t extra) message (r.1,r.2+739) =
      addTranscriptCalls (recordView t message r) (extra+739) := by
  cases t; cases r; simp [recordView,addTranscriptCalls,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem check_charge (pk : PublicKey) (t : Transcript submission.sizes)
    (candidate : Forgery submission.sizes) (extra : Nat) :
    referenceCheck pk (addTranscriptCalls t extra) candidate =
      (fun r => addResultCalls r extra) <$> referenceCheck pk t candidate := by
  cases candidate <;>
    simp only [referenceCheck,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  all_goals
    apply bind_congr
    intro result
    simp [addTranscriptCalls,addResultCalls,Transcript.freshMessage,Transcript.freshSignature,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Couple charged and base experiments using exactly the same signing, hash and private-coin answers.
The second result component accumulates only the repeated key-derivation overhead. -/
def interactTracked (scheme : Interface) (adversary : Adversary submission.sizes) (sk : SecretKey) (pk : PublicKey) :
    Nat → adversary.State → Transcript submission.sizes → Nat → OracleComp World (AttackResult × Nat)
  | 0,_,t,extra => pure (⟨false,t.hashCalls⟩,extra)
  | rounds+1,state,t,extra =>
    match adversary.step state with
    | .submit candidate => do
      let result ← (scheme.check pk t candidate).liftComp World
      pure (result,extra)
    | .hash input resume => do
      let answer ← liftM (HashSpec.query input)
      interactTracked scheme adversary sk pk rounds (resume answer) {t with hashCalls := t.hashCalls+1} extra
    | .sign request resume => do
      if t.signingRequests < LIFETIME then
        let result ← (scheme.sign sk pk request).liftComp World
        interactTracked scheme adversary sk pk rounds (resume result.1) (recordView t request.message result) (extra+739)
      else pure (⟨false,t.hashCalls⟩,extra)
    | .sample n resume => do
      let answer ← liftM (unifSpec.query n)
      interactTracked scheme adversary sk pk rounds (resume answer) t extra
    | .step next => interactTracked scheme adversary sk pk rounds next t extra

theorem tracked_base (scheme : Interface) (adversary : Adversary submission.sizes) (sk : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (t : Transcript submission.sizes) (extra : Nat) :
    Prod.fst <$> interactTracked scheme adversary sk pk rounds state t extra =
      interactWith scheme adversary sk pk rounds state t := by
  induction rounds generalizing state t extra with
  | zero => simp [interactTracked,interactWith]
  | succ rounds ih =>
    simp only [interactTracked,interactWith]
    cases h : adversary.step state <;> simp only [h]
    all_goals simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] at ih ⊢
    case submit candidate => simp only [bind_pure]
    case hash input resume => exact bind_congr (fun answer => ih _ _ _)
    case sign request resume =>
      split
      · rw [bind_assoc]
        exact bind_congr (fun result => ih _ _ _)
      · rfl
    case sample n resume => exact bind_congr (fun answer => ih _ _ _)
    case step next => exact ih _ _ _

theorem tracked_charged_generic (base charged : Interface)
    (hs : ∀ sk pk request, charged.sign sk pk request =
      (fun r => (r.1,r.2+739)) <$> base.sign sk pk request)
    (hc : ∀ pk t candidate extra, charged.check pk (addTranscriptCalls t extra) candidate =
      (fun r => addResultCalls r extra) <$> base.check pk t candidate)
    (adversary : Adversary submission.sizes) (sk : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (t : Transcript submission.sizes) (extra : Nat) :
    (fun r => addResultCalls r.1 r.2) <$> interactTracked base adversary sk pk rounds state t extra =
      interactWith charged adversary sk pk rounds state (addTranscriptCalls t extra) := by
  induction rounds generalizing state t extra with
  | zero => rfl
  | succ rounds ih =>
    simp only [interactTracked,interactWith]
    cases h : adversary.step state <;> simp only [h]
    all_goals simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] at ih ⊢
    case submit candidate =>
      rw [hc]
      simp only [map_eq_bind_pure_comp,OracleComp.liftComp_bind,OracleComp.liftComp_pure,
        Function.comp_def]
    case hash input resume =>
      apply bind_congr
      intro answer
      convert ih (resume answer) {t with hashCalls := t.hashCalls+1} extra using 1 <;>
        simp [addTranscriptCalls,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    case sign request resume =>
      simp only [addTranscriptCalls]
      split
      · rw [bind_assoc,hs]
        simp only [map_eq_bind_pure_comp,OracleComp.liftComp_bind,OracleComp.liftComp_pure,
          bind_assoc,pure_bind,Function.comp_def]
        apply bind_congr
        intro result
        change _ = interactWith charged adversary sk pk rounds (resume result.1)
          (recordView (addTranscriptCalls t extra) request.message (result.1,result.2+739))
        rw [record_charge]
        exact ih _ _ _
      · rfl
    case sample n resume => exact bind_congr (fun answer => ih _ _ _)
    case step next => exact ih _ _ _

theorem tracked_charged (adversary : Adversary submission.sizes) (sk : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (t : Transcript submission.sizes) (extra : Nat) :
    (fun r => addResultCalls r.1 r.2) <$>
      interactTracked baseReferenceInterface adversary sk pk rounds state t extra =
      interactWith referenceInterface adversary sk pk rounds state (addTranscriptCalls t extra) :=
  tracked_charged_generic baseReferenceInterface referenceInterface
    signing_charge check_charge adversary sk pk rounds state t extra

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.tracked_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracked_charged

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.tracked_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracked_base
/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.check_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_charge
end SigGolfCandidate.Hypertree.PreludeSecurity
