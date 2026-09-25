import SigGolfCandidate.Hypertree.KeygenFunctionalInitial
import SigGolfCandidate.Hypertree.KeygenFinish

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource
set_option maxRecDepth 4096

/-- Full exact keygen execution, with the reference public key in the organizer's output buffer. -/
theorem executes (hash : Hash) (secretKey : SecretKey) :
    ∃ final, Executes hash keygen (secretKeyState secretKey) 77097 ⟨.success,final,82446,739,761⟩ ∧
      ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64 := by
  obtain ⟨root,treeTrace,treePC,treeSP,words⟩ :=
    KeygenTree.execute hash (prefixState (secretKeyState secretKey)) (prefix_pc _ (secretKey_pc secretKey))
      (by rw [prefix_sp,secretKey_sp]) 159 0 secretKey (by decide) (prefix_context secretKey)
  have returned : root.pc=0x1014 := by rw [treePC,prefix_ra _ (secretKey_pc secretKey)]; decide
  refine ⟨Expansion.finishState (outputCopied root),
    executes_of_tree_trace hash (secretKeyState secretKey) root (secretKey_pc secretKey) 77073 82422 739 761 treeTrace returned,?_⟩
  intro i
  fin_cases i
  · rw [finish_mem]
    exact words 0
  · rw [finish_mem]
    exact words 1

theorem decode_publicKey (hash : Hash) (secretKey : SecretKey) (final : MachineState)
    (words : ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
      (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) :
    readBuffer final 0x40 16=Reference.keygen hash secretKey := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [Signing.getByte_word final 0x40 i (by decide) (by omega),words ⟨i/8,by omega⟩]
  exact KeygenNode.extractByte_slice (Reference.keygen hash secretKey) i

/-- The exact submitted keygen program returns the functional reference public key for every oracle and secret key. -/
theorem run_refines (hash : Hash) (secretKey : SecretKey) :
    ∃ cache : Cache, submission.runWith hash .keygen secretKey=
      ⟨some (Reference.keygen hash secretKey,cache),true,82446,739,761⟩ := by
  obtain ⟨final,trace,words⟩ := executes hash secretKey
  have run := runWith_of_executes submission hash .keygen secretKey (secretKeyState secretKey) 77097
    ⟨.success,final,82446,739,761⟩ (secretKey_loaded secretKey) trace (by decide)
  refine ⟨readBuffer final 0x60 CACHE_BYTES,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x40 16,readBuffer final 0x60 CACHE_BYTES),true,82446,739,761⟩ :
    RunResult (PublicKey×Cache)) = _
  rw [decode_publicKey hash secretKey final words]
  rfl

/-- Public-key-only formulation of the machine/reference correspondence. -/
theorem publicKey (hash : Hash) (secretKey : SecretKey) :
    ((submission.runWith hash .keygen secretKey).value.map Prod.fst)=some (Reference.keygen hash secretKey) := by
  obtain ⟨cache,run⟩ := run_refines hash secretKey
  rw [run]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenFunctional.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refines

end SigGolfCandidate.Hypertree.KeygenFunctional
