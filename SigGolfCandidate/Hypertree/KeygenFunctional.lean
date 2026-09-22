import SigGolfCandidate.Hypertree.KeygenFunctionalInitial
import SigGolfCandidate.Hypertree.KeygenFinish

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource
set_option maxRecDepth 4096

/-- Full exact keygen execution, with the reference public key in the organizer's output buffer. -/
theorem executes (hash : Hash) (seed : Seed) :
    ∃ final, Executes hash keygen (seedState seed) 75993 ⟨.success,final,81342,739,761⟩ ∧
      ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
        (Reference.keygen hash seed).extractLsb' (64*i.val) 64 := by
  obtain ⟨root,treeTrace,treePC,treeSP,words⟩ :=
    KeygenTree.execute hash (prefixState (seedState seed)) (prefix_pc _ (seed_pc seed))
      (by rw [prefix_sp,seed_sp]) 159 0 seed (by decide) (prefix_context seed)
  have returned : root.pc=0x1014 := by rw [treePC,prefix_ra _ (seed_pc seed)]; decide
  refine ⟨Expansion.finishState (outputCopied root),
    executes_of_tree_trace hash (seedState seed) root (seed_pc seed) 75969 81318 739 761 treeTrace returned,?_⟩
  intro i
  fin_cases i
  · rw [finish_mem]
    exact words 0
  · rw [finish_mem]
    exact words 1

theorem decode_publicKey (hash : Hash) (seed : Seed) (final : MachineState)
    (words : ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
      (Reference.keygen hash seed).extractLsb' (64*i.val) 64) :
    readBuffer final 0x40 16=Reference.keygen hash seed := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [Signing.getByte_word final 0x40 i (by decide) (by omega),words ⟨i/8,by omega⟩]
  exact KeygenNode.extractByte_slice (Reference.keygen hash seed) i

/-- The exact submitted keygen program returns the functional reference public key for every oracle and seed. -/
theorem run_refines (hash : Hash) (seed : Seed) :
    ∃ cache : Cache, submission.runWith hash .keygen seed=
      ⟨some (Reference.keygen hash seed,cache),true,81342,739,761⟩ := by
  obtain ⟨final,trace,words⟩ := executes hash seed
  have run := runWith_of_executes submission hash .keygen seed (seedState seed) 75993
    ⟨.success,final,81342,739,761⟩ (seed_loaded seed) trace (by decide)
  refine ⟨readBuffer final 0x60 CACHE_BYTES,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x40 16,readBuffer final 0x60 CACHE_BYTES),true,81342,739,761⟩ :
    RunResult (PublicKey×Cache)) = _
  rw [decode_publicKey hash seed final words]
  rfl

/-- Public-key-only formulation of the machine/reference correspondence. -/
theorem publicKey (hash : Hash) (seed : Seed) :
    ((submission.runWith hash .keygen seed).value.map Prod.fst)=some (Reference.keygen hash seed) := by
  obtain ⟨cache,run⟩ := run_refines hash seed
  rw [run]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenFunctional.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refines

end SigGolfCandidate.Hypertree.KeygenFunctional
