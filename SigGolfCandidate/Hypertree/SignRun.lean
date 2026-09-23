import SigGolfCandidate.Hypertree.SignExecution
import SigGolfCandidate.Hypertree.SignWire

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying SignatureEncoding
set_option maxRecDepth 4096

/-- Exact official signer output for arbitrary secretKeys, public keys, caches, messages, and oracles. -/
theorem sign_run_refines (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16922843 ∧ submission.runWith hash .sign (secretKey,pk,cache,message)=
      ⟨if Reference.keygen hash secretKey=pk then
        some ((signCompact hash secretKey pk message).wire (signCompact_valid hash secretKey pk message)) else none,
        true,cycles,111596,114920⟩ := by
  obtain ⟨initial,final,instructions,cycles,loaded,execution,ib,cb,stored,randomizer⟩ :=
    sign_execution hash secretKey pk cache message
  have run := runWith_of_executes submission hash .sign (secretKey,pk,cache,message) initial instructions
    ⟨if Reference.keygen hash secretKey=pk then .success else .failure,final,cycles,111596,114920⟩ loaded execution
    (by unfold CYCLE_LIMIT; omega)
  have output := SignWire.read_sign hash final secretKey pk message randomizer stored
  refine ⟨cycles,cb,?_⟩
  rw [run]
  by_cases same : Reference.keygen hash secretKey=pk
  · simp only [if_pos same]
    change (⟨some (readBuffer final 0x20060 signatureBytes),true,cycles,111596,114920⟩ :
      RunResult (Bytes signatureBytes)) = _
    rw [output]
    rfl
  · simp only [if_neg same]
    rfl

/-- Honest signer execution succeeds for every fixed oracle, with no cache assumptions. -/
theorem sign_run_honest (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16922843 ∧ submission.runWith hash .sign (secretKey,Reference.keygen hash secretKey,cache,message)=
      ⟨some ((signCompact hash secretKey (Reference.keygen hash secretKey) message).wire
        (signCompact_valid hash secretKey (Reference.keygen hash secretKey) message)),true,cycles,111596,114920⟩ := by
  simpa using sign_run_refines hash secretKey (Reference.keygen hash secretKey) cache message

/-- Universal actual signer termination and exact hash-resource accounting. -/
theorem sign_run_bound (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) :
    let result := submission.runWith hash .sign (secretKey,pk,cache,message)
    result.finished=true ∧ result.cycles≤16922843 ∧ result.cycles<CYCLE_LIMIT ∧
      result.hashCalls=111596 ∧ result.hashCompressions=114920 ∧ result.hashCompressions≤BUDGET_SIGN := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash secretKey pk cache message
  dsimp only
  rw [run]
  dsimp only
  exact ⟨rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_run_refines
end SigGolfCandidate.Hypertree.Signing
