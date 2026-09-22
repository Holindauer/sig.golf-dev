import SigGolfCandidate.Hypertree.SignExecution
import SigGolfCandidate.Hypertree.SignWire

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying SignatureEncoding
set_option maxRecDepth 4096

/-- Exact official signer output for arbitrary seeds, public keys, caches, messages, and oracles. -/
theorem sign_run_refines (hash : Hash) (seed : Seed) (pk : PublicKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16800271 ∧ submission.runWith hash .sign (seed,pk,cache,message)=
      ⟨if Reference.keygen hash seed=pk then
        some ((signCompact hash seed pk message).wire (signCompact_valid hash seed pk message)) else none,
        true,cycles,117508,121008⟩ := by
  obtain ⟨initial,final,instructions,cycles,loaded,execution,ib,cb,stored,randomizer⟩ :=
    sign_execution hash seed pk cache message
  have run := runWith_of_executes submission hash .sign (seed,pk,cache,message) initial instructions
    ⟨if Reference.keygen hash seed=pk then .success else .failure,final,cycles,117508,121008⟩ loaded execution
    (by unfold CYCLE_LIMIT; omega)
  have output := SignWire.read_sign hash final seed pk message randomizer stored
  refine ⟨cycles,cb,?_⟩
  rw [run]
  by_cases same : Reference.keygen hash seed=pk
  · simp only [if_pos same]
    change (⟨some (readBuffer final 0x20060 signatureBytes),true,cycles,117508,121008⟩ :
      RunResult (Bytes signatureBytes)) = _
    rw [output]
    rfl
  · simp only [if_neg same]
    rfl

/-- Honest signer execution succeeds for every fixed oracle, with no cache assumptions. -/
theorem sign_run_honest (hash : Hash) (seed : Seed) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16800271 ∧ submission.runWith hash .sign (seed,Reference.keygen hash seed,cache,message)=
      ⟨some ((signCompact hash seed (Reference.keygen hash seed) message).wire
        (signCompact_valid hash seed (Reference.keygen hash seed) message)),true,cycles,117508,121008⟩ := by
  simpa using sign_run_refines hash seed (Reference.keygen hash seed) cache message

/-- Universal actual signer termination and exact hash-resource accounting. -/
theorem sign_run_bound (hash : Hash) (seed : Seed) (pk : PublicKey) (cache : Cache) (message : Message) :
    let result := submission.runWith hash .sign (seed,pk,cache,message)
    result.finished=true ∧ result.cycles≤16800271 ∧ result.cycles<CYCLE_LIMIT ∧
      result.hashCalls=117508 ∧ result.hashCompressions=121008 ∧ result.hashCompressions≤BUDGET_SIGN := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash seed pk cache message
  dsimp only
  rw [run]
  dsimp only
  exact ⟨rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_run_refines
end SigGolfCandidate.Hypertree.Signing
