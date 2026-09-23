import SigGolfCandidate.Hypertree.KeygenFunctional

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource
set_option maxRecDepth 4096

/-- The candidate's public cache contains no secret key-dependent state. -/
def zeroCache : Cache := 0

theorem decode_zero_cache (s : MachineState)
    (zero : ∀ a : Word, 0x60 ≤ a.toNat → a.toNat < 0x80000 → s.getMem a=0) :
    readBuffer s 0x60 CACHE_BYTES=zeroCache := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  have hi' : i < 131072 := hi
  rw [Signing.getByte_word s 0x60 i (by decide) (by omega)]
  have lower : 0x60 ≤ (Signing.wordAddress 0x60 (i/8)).toNat := by
    change 0x60 ≤ (0x60+8*(i/8))%2^64
    omega
  have upper : (Signing.wordAddress 0x60 (i/8)).toNat < 0x80000 := by
    change (0x60+8*(i/8))%2^64 < 0x80000
    omega
  rw [zero _ lower upper]
  simp [zeroCache, extractByte]

theorem executes_zero_cache (hash : Hash) (secretKey : SecretKey) :
    ∃ final, Executes hash keygen (secretKeyState secretKey) 77097 ⟨.success,final,82446,739,761⟩ ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      readBuffer final 0x60 CACHE_BYTES=zeroCache := by
  obtain ⟨root,treeTrace,treePC,treeSP,words,frame⟩ :=
    KeygenTree.execute_framed hash (prefixState (secretKeyState secretKey)) (prefix_pc _ (secretKey_pc secretKey))
      (by rw [prefix_sp,secretKey_sp]) 159 0 secretKey (by decide) (prefix_context secretKey)
  have returned : root.pc=0x1014 := by rw [treePC,prefix_ra _ (secretKey_pc secretKey)]; decide
  refine ⟨Expansion.finishState (outputCopied root),
    executes_of_tree_trace hash (secretKeyState secretKey) root (secretKey_pc secretKey) 77073 82422 739 761 treeTrace returned,?_,?_⟩
  · intro i
    fin_cases i
    · rw [finish_mem]; exact words 0
    · rw [finish_mem]; exact words 1
  · apply decode_zero_cache
    intro a lower upper
    have h40 : a ≠ 0x40 := by intro eq; rw [eq] at lower; change 0x60 ≤ 0x40 at lower; omega
    have h48 : a ≠ 0x48 := by intro eq; rw [eq] at lower; change 0x60 ≤ 0x48 at lower; omega
    have hl : a ≠ 0x80400 := by intro eq; rw [eq] at upper; change 0x80400 < 0x80000 at upper; omega
    rw [finish_mem,if_neg h48,if_neg h40,frame a upper,prefix_mem,if_neg hl]
    exact secretKey_zero secretKey a (by omega)

/-- Exact typed key generation, including its canonical zero cache. -/
theorem run_exact (hash : Hash) (secretKey : SecretKey) :
    submission.runWith hash .keygen secretKey =
      ⟨some (Reference.keygen hash secretKey,zeroCache),true,82446,739,761⟩ := by
  obtain ⟨final,trace,words,cache⟩ := executes_zero_cache hash secretKey
  have run := runWith_of_executes submission hash .keygen secretKey (secretKeyState secretKey) 77097
    ⟨.success,final,82446,739,761⟩ (secretKey_loaded secretKey) trace (by decide)
  rw [run]
  change (⟨some (readBuffer final 0x40 16,readBuffer final 0x60 CACHE_BYTES),true,82446,739,761⟩ :
    RunResult (PublicKey×Cache)) = _
  rw [decode_publicKey hash secretKey final words,cache]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenFunctional.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exact

end SigGolfCandidate.Hypertree.KeygenFunctional
