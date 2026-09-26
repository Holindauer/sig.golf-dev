import SigGolfCandidate.Hypertree.PreludeSecurityCoupling
import SigGolfCandidate.Hypertree.PreludeSecurityReference

namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode Signing.Prelude SecurityCache SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem observe_uniform_bind {α β : Type} (program : ProbComp α) (next : α → OracleComp World β)
    (cache : QueryCache HashSpec) :
    observe (program.liftComp World >>= next) cache =
      (program >>= fun value => observe (next value) cache) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [observe]
  | query_bind n continuation ih =>
    rw [OracleComp.liftComp_bind,bind_assoc]
    change observe ((liftM (unifSpec.query n) : OracleComp World _) >>= _) cache = _
    rw [observe_coin_bind,bind_assoc]
    apply bind_congr
    intro answer
    exact ih answer

def secretKeyedWith (scheme : Interface) (adversary : Adversary submission.sizes) (rounds : Nat) (secretKey : SecretKey) :
    OracleComp World AttackResult := do
  let result ← (scheme.keygen secretKey).liftComp World
  let some (pk,cache) := result.1 | pure ⟨false,result.2⟩
  interactWith scheme adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=result.2}

theorem experiment_secretKeyed (scheme : Interface) (adversary : Adversary submission.sizes) (rounds : Nat) :
    experimentWith scheme adversary rounds = (do let secretKey←sampleSecretKey; observe (secretKeyedWith scheme adversary rounds secretKey) ∅) := by
  change observe (sampleSecretKey.liftComp World >>= fun secretKey => secretKeyedWith scheme adversary rounds secretKey) ∅ = _
  exact observe_uniform_bind sampleSecretKey _ ∅

/-- Generic initial-key coupling. Both continuations use the same generated key,
cache, and initial query counter; cached key knowledge justifies adaptive signing. -/
theorem secretKeyed_equivalent_generic (left right : Interface) (adversary : Adversary submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) (fact : PublicKey → Hash → Prop)
    (keyEq : ∀ hash, evalWithAnswerFn hash (left.keygen secretKey)=evalWithAnswerFn hash (right.keygen secretKey))
    (keyKnown : ∀ result ∈ support (runHash (right.keygen secretKey) ∅),
      ∀ pk cache, result.1.1=some (pk,cache) → Knows result.2 (fact pk))
    (signEq : ∀ pk hash, fact pk hash → ∀ request,
      evalWithAnswerFn hash (left.sign secretKey pk request)=evalWithAnswerFn hash (right.sign secretKey pk request))
    (checkEq : ∀ pk hash transcript candidate,
      evalWithAnswerFn hash (left.check pk transcript candidate)=evalWithAnswerFn hash (right.check pk transcript candidate)) :
    𝒮[observe (secretKeyedWith left adversary rounds secretKey) ∅]=𝒮[observe (secretKeyedWith right adversary rounds secretKey) ∅] := by
  unfold secretKeyedWith
  calc
    _ = 𝒮[observe ((right.keygen secretKey).liftComp World >>= fun result =>
      match result.1 with
      | some (pk,cache) => interactWith left adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=result.2}
      | _ => pure ⟨false,result.2⟩) ∅] :=
      contextual_equivalence _ _ keyEq _ ∅
    _ = _ := by
      rw [observe_hash_bind,observe_hash_bind]
      apply evalSPMF_bind_congr
      intro result mem
      cases value : result.1.1 with
      | none => rfl
      | some pair =>
        rcases pair with ⟨pk,cache⟩
        simp only
        exact interact_equivalent_generic left right (fact pk) adversary secretKey pk rounds
          (adversary.initial pk cache) {hashCalls:=result.1.2} result.2 (keyKnown result mem pk cache value)
          (signEq pk) (checkEq pk)

theorem secretKeyed_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) (secretKey : SecretKey) :
    𝒮[observe (secretKeyedWith actualInterface adversary rounds secretKey) ∅]=
      𝒮[observe (secretKeyedWith referenceInterface adversary rounds secretKey) ∅] := by
  apply secretKeyed_equivalent_generic actualInterface referenceInterface adversary rounds secretKey
    (fun pk hash => Reference.keygen hash secretKey=pk) (fun hash => keygen_equivalent hash secretKey)
  · intro result mem pk cache value hash agree
    have eq := (runHash_support_agrees (referenceInterface.keygen secretKey) ∅ result mem hash agree).2
    have publicEq := congrArg (fun output => output.1.map Prod.fst) eq
    simp only [referenceInterface,referenceKeygen,evalWithAnswerFn_bind,evalWithAnswerFn_pure,
      eval_countHash,SecurityReference.eval_keygen,value,Option.map_some] at publicEq
    exact Option.some.inj publicEq
  · intro pk hash valid request; exact sign_equivalent hash secretKey pk request valid
  · intro pk hash transcript candidate; exact check_equivalent hash pk transcript candidate

/-- Exact shared-random-oracle security distribution. This includes private coins,
both forgery forms, supplied caches, replay history, lifetime, and total call counts. -/
theorem experiment_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[preludeSubmission.securityExperiment adversary rounds]=𝒮[experimentWith referenceInterface adversary rounds] := by
  rw [←actual_experiment,experiment_secretKeyed,experiment_secretKeyed]
  apply evalSPMF_bind_congr
  intro secretKey _
  exact secretKeyed_equivalent adversary rounds secretKey

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.experiment_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms experiment_equivalent
end SigGolfCandidate.Hypertree.PreludeSecurity
