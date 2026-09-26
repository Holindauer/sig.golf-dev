import SigGolf.Programs
import SigGolfCandidate.Hypertree.PreludeCandidatePhases
namespace SigGolfCandidate.Hypertree.PreludeCandidate
open SigGolf OracleComp
set_option maxRecDepth 4096
def pipeline {σ ω : Type} (loading : Nat) (keygen : OracleComp HashSpec (RunResult (PublicKey × Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit)) : OracleComp HashSpec HonestResult := do
  let keygen ← keygen
  let costs := recordCost (fun _ => 0) .keygen keygen.hashCompressions
  let some (pk,cache) := keygen.value | return ⟨false,costs,0⟩
  let sign ← sign pk cache
  let costs := recordCost costs .sign sign.hashCompressions
  let some signature := sign.value | return ⟨false,costs,0⟩
  let expand ← expand pk signature
  let costs := recordCost costs .expand expand.hashCompressions
  let some witness := expand.value | return ⟨false,costs,0⟩
  let verify ← verify pk witness
  return ⟨verify.value.isSome,recordCost costs .verify verify.hashCompressions,verify.cycles + loading⟩

theorem honest_eq_pipeline (s : Submission) (secretKey : SecretKey) (message : Message) :
    s.honest secretKey message = pipeline (witnessCycles s.sizes.witness) (s.run .keygen secretKey)
      (fun pk cache => s.run .sign (secretKey,cache,message))
      (fun pk signature => s.run .expand (message,pk,signature))
      (fun pk witness => s.run .verify (message,pk,witness)) := by
  simp only [Submission.honest,pipeline]
  congr 1
  funext kg
  rcases kg.value with _ | ⟨pk,cache⟩
  · rfl
  · dsimp only
    congr 1
    funext sg
    cases sg.value with
    | none => rfl
    | some signature =>
      dsimp only
      congr 1
      funext ex
      cases ex.value with
      | none => rfl
      | some witness => rfl

theorem pipeline_success {σ ω : Type} (loading : Nat) (hash : Hash) (keygen : OracleComp HashSpec (RunResult (PublicKey×Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit))
    (pk : PublicKey) (cache : Cache) (signature : σ) (witness : ω)
    (kc kh kb sc sh sb ec eh eb vc vh vb : Nat)
    (kg : evalWithAnswerFn hash keygen=⟨some (pk,cache),true,kc,kh,kb⟩)
    (sg : evalWithAnswerFn hash (sign pk cache)=⟨some signature,true,sc,sh,sb⟩)
    (ex : evalWithAnswerFn hash (expand pk signature)=⟨some witness,true,ec,eh,eb⟩)
    (vr : evalWithAnswerFn hash (verify pk witness)=⟨some (),true,vc,vh,vb⟩) :
    evalWithAnswerFn hash (pipeline loading keygen sign expand verify)=
      ⟨true,fun phase => match phase with | .keygen => kb | .sign => sb | .expand => eb | .verify => vb,vc+loading⟩ := by
  simp only [pipeline,evalWithAnswerFn_bind,kg,sg,ex,vr,evalWithAnswerFn_pure]
  congr 1
  funext phase
  cases phase <;> rfl


/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.honest_eq_pipeline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_eq_pipeline
/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.pipeline_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pipeline_success
end SigGolfCandidate.Hypertree.PreludeCandidate
