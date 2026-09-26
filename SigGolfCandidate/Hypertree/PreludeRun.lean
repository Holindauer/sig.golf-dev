import SigGolfCandidate.Hypertree.PreludeExecution
import SigGolfCandidate.Hypertree.SignWire
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying SignatureEncoding
set_option maxRecDepth 4096

theorem loaded_exists (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ s, initialState preludeSubmission .sign (secretKey,cache,message) = some s := by
  unfold initialState
  rw [if_pos sign_valid]
  exact ⟨_,rfl⟩

theorem sign_run_refines (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤17028613 ∧ preludeSubmission.runWith hash .sign (secretKey,cache,message)=
      ⟨some ((signCompact hash secretKey (Reference.keygen hash secretKey) message).wire
        (signCompact_valid hash secretKey (Reference.keygen hash secretKey) message)),true,cycles,118247,121769⟩ := by
  obtain ⟨initial,loaded⟩ := loaded_exists secretKey cache message
  obtain ⟨final,instructions,cycles,execution,ib,cb,stored,randomizer⟩ :=
    sign_execution hash secretKey cache message initial loaded
  have run := runWith_of_executes preludeSubmission hash .sign (secretKey,cache,message) initial instructions
    ⟨.success,final,cycles,118247,121769⟩ loaded execution (by unfold CYCLE_LIMIT; omega)
  have output := SignWire.read_sign hash final secretKey (Reference.keygen hash secretKey) message randomizer stored
  refine ⟨cycles,cb,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x20060 signatureBytes),true,cycles,118247,121769⟩ :
    RunResult (Bytes signatureBytes)) = _
  rw [output]
  rfl

theorem sign_run_bound (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    let result := preludeSubmission.runWith hash .sign (secretKey,cache,message)
    result.finished=true ∧ result.cycles≤17028613 ∧ result.cycles<CYCLE_LIMIT ∧
      result.hashCalls=118247 ∧ result.hashCompressions=121769 ∧ result.hashCompressions≤BUDGET_SIGN := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash secretKey cache message
  dsimp only
  rw [run]
  dsimp only
  exact ⟨rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_run_refines
/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_run_bound
end SigGolfCandidate.Hypertree.Signing.Prelude
