import SigGolfCandidate.Hypertree.CandidateHonest

namespace SigGolfCandidate.Hypertree.Candidate
open SigGolf OracleComp KeygenOrganizer
set_option maxRecDepth 4096

/-- All four exact submitted images finish below the official cycle limit on every typed input. -/
theorem termination : submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    rw [KeygenFunctional.run_exact hash input]
    dsimp only
    exact ⟨rfl,by decide⟩
  | sign =>
    rcases input with ⟨secretKey,pk,cache,message⟩
    have bound := Signing.sign_run_bound hash secretKey pk cache message
    exact ⟨bound.1,bound.2.2.1⟩
  | expand =>
    have bound := Expansion.run_bound hash input
    exact ⟨bound.1,by rw [bound.2.2.1]; decide⟩
  | verify =>
    rcases input with ⟨message,pk,witness⟩
    obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := Verifying.run_refines hash pk message witness
    rw [run]
    dsimp only
    exact ⟨rfl,by unfold CYCLE_LIMIT; omega⟩

/-- The actual shared-random-oracle, all-message completeness statement. -/
theorem completeness : submission.Complete := by
  apply complete_of_honest_success
  intro hash secretKey message
  obtain ⟨cycles,calls,blocks,_,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]

/-- Uniform honest costs imply the exponential budget for an independent uniform message. -/
theorem compressionBounds : submission.CompressionBounds := by
  apply compressionBounds_of_honest_cost
  intro hash secretKey message phase budgeted
  obtain ⟨cycles,calls,blocks,_,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  cases phase with
  | keygen => change 761≤BUDGET_KEYGEN; decide
  | sign => change 121008≤BUDGET_SIGN; decide
  | expand => exact Nat.zero_le _
  | verify => simp [Phase.budgeted] at budgeted

/-- Honest verification is bounded by the universal exact-bytecode verifier bound. -/
theorem verificationBound : submission.VerificationBound 5652800 := by
  intro hash secretKey message
  dsimp only
  intro _
  obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  exact cycleBound

/-- This conditional assembly deliberately requires the organizer's actual security theorem. -/
theorem certificate_of_secure (security : submission.Secure) : Certificate submission 5652800 :=
  ⟨admitted,termination,completeness,compressionBounds,security,verificationBound⟩

/-- info: 'SigGolfCandidate.Hypertree.Candidate.termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termination
/-- info: 'SigGolfCandidate.Hypertree.Candidate.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completeness
/-- info: 'SigGolfCandidate.Hypertree.Candidate.compressionBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compressionBounds
/-- info: 'SigGolfCandidate.Hypertree.Candidate.verificationBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verificationBound
end SigGolfCandidate.Hypertree.Candidate
