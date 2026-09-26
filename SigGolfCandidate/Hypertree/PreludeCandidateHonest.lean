import SigGolfCandidate.Hypertree.PreludePipeline
namespace SigGolfCandidate.Hypertree.PreludeCandidate
open SigGolf OracleComp SignatureEncoding Signing.Prelude
set_option maxRecDepth 4096
theorem honest_exact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks, cycles≤1591711 ∧ calls≤51841 ∧ blocks≤53602 ∧
      evalWithAnswerFn hash (preludeSubmission.honest secretKey message)=
        ⟨true,fun phase => match phase with | .keygen => 761 | .sign => 121769 | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := Reference.keygen hash secretKey
  let signature := (signCompact hash secretKey pk message).wire (signCompact_valid hash secretKey pk message)
  obtain ⟨sc,_,sg⟩ := sign_run_refines hash secretKey KeygenFunctional.zeroCache message
  obtain ⟨vc,hc,hb,cb,hcb,hbb,vr⟩ := Verifying.run_refines_charged hash pk message signature
  have correct : Reference.verify hash pk message (decode signature).toReference := by
    rw [wire_decode]; exact signCompact_correct hash secretKey message
  rw [if_pos correct] at vr
  have kg := (keygen_eq hash secretKey).trans (KeygenFunctional.run_exact hash secretKey)
  have ex := expand_exact hash message pk signature
  have ver := (verify_eq hash (message,pk,signature)).trans vr
  refine ⟨vc+witnessCycles signatureBytes,hc,hb,cb,hcb,hbb,?_⟩
  rw [honest_eq_pipeline]
  exact pipeline_success (witnessCycles signatureBytes) hash (preludeSubmission.run .keygen secretKey)
    (fun _ c => preludeSubmission.run .sign (secretKey,c,message))
    (fun p sig => preludeSubmission.run .expand (message,p,sig))
    (fun p wit => preludeSubmission.run .verify (message,p,wit))
    pk KeygenFunctional.zeroCache signature signature
    82446 739 761 sc 118247 121769 89733 0 0 vc hc hb kg sg ex ver

/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.honest_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_exact
end SigGolfCandidate.Hypertree.PreludeCandidate
