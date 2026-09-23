import SigGolfCandidate.Hypertree.SignRun
import SigGolfCandidate.Hypertree.VerifyFunctional
import SigGolfCandidate.Hypertree.KeygenExpandOrganizer

namespace SigGolfCandidate.Hypertree.Candidate
open SigGolf OracleComp KeygenOrganizer SignatureEncoding
set_option maxRecDepth 4096

theorem expand_exact (hash : Hash) (message : Message) (pk : PublicKey) (signature : Bytes signatureBytes) :
    submission.runWith hash .expand (message,pk,signature)=⟨some signature,true,89733,0,0⟩ := by
  have value := Expansion.run_identity hash (message,pk,signature)
  obtain ⟨finished,_,cycles,calls,blocks⟩ := Expansion.run_bound hash (message,pk,signature)
  cases h : submission.runWith hash .expand (message,pk,signature)
  simp only [h] at value finished cycles calls blocks
  cases value
  cases finished
  cases cycles
  cases calls
  cases blocks
  rfl

/-- Exact deterministic evaluation of a successful organizer pipeline. -/
theorem pipeline_success {σ ω : Type} (hash : Hash) (keygen : OracleComp HashSpec (RunResult (PublicKey×Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit))
    (pk : PublicKey) (cache : Cache) (signature : σ) (witness : ω)
    (kc kh kb sc sh sb ec eh eb vc vh vb : Nat)
    (kg : evalWithAnswerFn hash keygen=⟨some (pk,cache),true,kc,kh,kb⟩)
    (sg : evalWithAnswerFn hash (sign pk cache)=⟨some signature,true,sc,sh,sb⟩)
    (ex : evalWithAnswerFn hash (expand pk signature)=⟨some witness,true,ec,eh,eb⟩)
    (vr : evalWithAnswerFn hash (verify pk witness)=⟨some (),true,vc,vh,vb⟩) :
    evalWithAnswerFn hash (pipeline keygen sign expand verify)=
      ⟨true,fun phase => match phase with | .keygen => kb | .sign => sb | .expand => eb | .verify => vb,vc⟩ := by
  simp only [pipeline,evalWithAnswerFn_bind,kg,sg,ex,vr,evalWithAnswerFn_pure]
  congr 1
  funext phase
  cases phase <;> rfl

/-- Every message succeeds against each single fixed oracle, with exact budgeted-phase costs. -/
theorem honest_exact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks, cycles≤3218131 ∧ calls≤51841 ∧ blocks≤53602 ∧
      evalWithAnswerFn hash (submission.honest secretKey message)=
        ⟨true,fun phase => match phase with | .keygen => 761 | .sign => 121008 | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := Reference.keygen hash secretKey
  let signature := (signCompact hash secretKey pk message).wire (signCompact_valid hash secretKey pk message)
  obtain ⟨signCycles,_,signRun⟩ := Signing.sign_run_honest hash secretKey KeygenFunctional.zeroCache message
  obtain ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,verifyRun⟩ := Verifying.run_refines hash pk message signature
  have correct : Reference.verify hash pk message (decode signature).toReference := by
    rw [wire_decode]
    exact signCompact_correct hash secretKey message
  rw [if_pos correct] at verifyRun
  refine ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,?_⟩
  rw [honest_eq_pipeline]
  exact pipeline_success hash (submission.run .keygen secretKey)
    (fun p c => submission.run .sign (secretKey,p,c,message))
    (fun p sig => submission.run .expand (message,p,sig))
    (fun p wit => submission.run .verify (message,p,wit)) pk KeygenFunctional.zeroCache signature signature
    82446 739 761 signCycles 117508 121008 89733 0 0 cycles calls blocks
    (KeygenFunctional.run_exact hash secretKey) signRun (expand_exact hash message pk signature) verifyRun

/-- info: 'SigGolfCandidate.Hypertree.Candidate.honest_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_exact
end SigGolfCandidate.Hypertree.Candidate
