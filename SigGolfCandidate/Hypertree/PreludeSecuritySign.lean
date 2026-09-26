import SigGolfCandidate.Hypertree.PreludeRun
import SigGolfCandidate.Hypertree.SecurityBytecodeCounts
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp Reference SignatureEncoding SecurityVerifyCost Signing.Prelude
set_option maxRecDepth 4096

/-- Reference signing explicitly repeats public-key derivation, as the new ABI requires. -/
def signDerived (secretKey : SecretKey) (message : Message) : OracleComp HashSpec Compact := do
  let pk ← SecurityReference.keygen secretKey
  SecurityReference.signCompact secretKey pk message

theorem eval_signDerived (hash : Hash) (secretKey : SecretKey) (message : Message) :
    evalWithAnswerFn hash (signDerived secretKey message) =
      signCompact hash secretKey (Reference.keygen hash secretKey) message := by
  simp [signDerived,evalWithAnswerFn_bind]

theorem calls_signDerived (hash : Hash) (secretKey : SecretKey) (message : Message) :
    calls hash (signDerived secretKey message) = 118247 := by
  simp [signDerived,calls_bind,SecurityBytecodeCounts.calls_keygen,SecurityBytecodeCounts.calls_signCompact]

/-- The actual signing result and query count equal the derived-key reference for every cache. -/
theorem signing_view (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    let actual := preludeSubmission.runWith hash .sign (secretKey,cache,message)
    actual.value = some ((signCompact hash secretKey (Reference.keygen hash secretKey) message).wire
      (signCompact_valid hash secretKey (Reference.keygen hash secretKey) message)) ∧
    actual.hashCalls = calls hash (signDerived secretKey message) := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash secretKey cache message
  dsimp only
  rw [run,calls_signDerived]
  exact ⟨rfl,rfl⟩

/-- Exact overhead against the existing signing game; this equality must be
carried through adaptive transcripts before applying the old budget bound. -/
theorem signing_overhead (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message)
    (pk : PublicKey) (validKey : Reference.keygen hash secretKey = pk) :
    let actual := preludeSubmission.runWith hash .sign (secretKey,cache,message)
    actual.value = some ((signCompact hash secretKey pk message).wire
      (signCompact_valid hash secretKey pk message)) ∧
    actual.hashCalls = calls hash (SecurityReference.signCompact secretKey pk message) + 739 := by
  obtain ⟨value,count⟩ := signing_view hash secretKey cache message
  dsimp only at value count ⊢
  rw [validKey] at value
  refine ⟨value,?_⟩
  rw [count,calls_signDerived,SecurityBytecodeCounts.calls_signCompact]

/-- For any common prior transcript, the original reference charge is a lower
bound on the actual charge, including all repeated public-key derivation calls. -/
theorem signing_budget_domination (hash : Hash) (secretKey : SecretKey) (cache : Cache)
    (message : Message) (pk : PublicKey) (validKey : Reference.keygen hash secretKey = pk)
    (prior budget : Nat)
    (within : prior + (preludeSubmission.runWith hash .sign (secretKey,cache,message)).hashCalls ≤ budget) :
    prior + calls hash (SecurityReference.signCompact secretKey pk message) ≤ budget := by
  have count := (signing_overhead hash secretKey cache message pk validKey).2
  omega

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.calls_signDerived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calls_signDerived
/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.signing_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_view
/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.signing_budget_domination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_budget_domination
end SigGolfCandidate.Hypertree.PreludeSecurity
