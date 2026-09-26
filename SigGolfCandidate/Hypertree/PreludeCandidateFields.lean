import SigGolfCandidate.Hypertree.PreludeOrganizerBridges

namespace SigGolfCandidate.Hypertree.PreludeCandidate
open SigGolf OracleComp Signing.Prelude
set_option maxRecDepth 4096

/-- All four exact submitted images finish below the official cycle limit on every typed input. -/
theorem termination : preludeSubmission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    change (submission.runWith hash .keygen input).finished = true ∧ (submission.runWith hash .keygen input).cycles < CYCLE_LIMIT
    rw [KeygenFunctional.run_exact hash input]
    dsimp only
    exact ⟨rfl,by decide⟩
  | sign =>
    rcases input with ⟨secretKey,cache,message⟩
    have bound := Signing.Prelude.sign_run_bound hash secretKey cache message
    exact ⟨bound.1,bound.2.2.1⟩
  | expand =>
    change (submission.runWith hash .expand input).finished = true ∧ (submission.runWith hash .expand input).cycles < CYCLE_LIMIT
    have bound := Expansion.run_bound hash input
    exact ⟨bound.1,by rw [bound.2.2.1]; decide⟩
  | verify =>
    rcases input with ⟨message,pk,witness⟩
    obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := Verifying.run_refines hash pk message witness
    change (submission.runWith hash .verify (message,pk,witness)).finished = true ∧ (submission.runWith hash .verify (message,pk,witness)).cycles < CYCLE_LIMIT
    rw [run]
    dsimp only
    exact ⟨rfl,by unfold CYCLE_LIMIT; omega⟩

/-- The actual shared-random-oracle, all-message completeness statement. -/
theorem completeness : preludeSubmission.Complete := by
  apply complete_of_honest_success
  intro hash secretKey message
  obtain ⟨cycles,calls,blocks,_,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]

/-- Uniform honest costs imply the exponential budget for an independent uniform message. -/
theorem compressionBounds : preludeSubmission.CompressionBounds := by
  apply compressionBounds_of_honest_cost
  intro hash secretKey message phase budgeted
  obtain ⟨cycles,calls,blocks,_,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  cases phase with
  | keygen => change 761≤BUDGET_KEYGEN; decide
  | sign => change 121769≤BUDGET_SIGN; decide
  | expand => exact Nat.zero_le _
  | verify => simp [Phase.budgeted] at budgeted

/-- Honest verification is bounded by the universal exact-bytecode verifier bound. -/
theorem verificationBound : preludeSubmission.VerificationBound 1591711 := by
  intro hash secretKey message
  dsimp only
  intro _
  obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  exact cycleBound

/-- This conditional assembly deliberately requires the organizer's actual security theorem. -/
theorem certificate_of_secure (security : preludeSubmission.Secure) : Certificate preludeSubmission 1591711 :=
  ⟨admitted,termination,completeness,compressionBounds,security,verificationBound⟩

/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms termination
/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completeness
/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.compressionBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionBounds
/-- info: 'SigGolfCandidate.Hypertree.PreludeCandidate.verificationBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationBound
end SigGolfCandidate.Hypertree.PreludeCandidate
