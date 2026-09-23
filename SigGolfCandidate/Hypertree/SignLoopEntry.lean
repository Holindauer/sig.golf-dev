import SigGolfCandidate.Hypertree.SignPrefixRefine

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem loaded_scratch (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState submission .sign (secretKey,pk,cache,message) = some s)
    (a : Word) (high : 0x80000 ≤ a.toNat) : s.getMem a = 0 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .sign)] at loaded
  cases Option.some.inj loaded
  dsimp only [inputBuffers,List.foldl_cons,List.foldl_nil]
  rw [MachineState.getMem_setReg]
  dsimp only [submission]
  rw [Memory.write_preserves _ 0 (bytes message) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [Memory.write_preserves _ 0x60 (bytes cache) a
    (by rw [Memory.bytes_length (n := CACHE_BYTES)]; decide)
    (by right; rw [Memory.bytes_length (n := CACHE_BYTES)]; change 131168 ≤ a.toNat; omega)]
  rw [Memory.write_preserves _ 0x40 (bytes pk) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [Memory.write_preserves _ 0x20 (bytes secretKey) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [show sign.data = [] by rfl,MachineState.writeBytesAsWords_nil]
  rfl

theorem loaded_stack (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState submission .sign (secretKey,pk,cache,message) = some s) :
    s.getReg .x2 = 0x1000000 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .sign)] at loaded
  cases Option.some.inj loaded
  rw [MachineState.getReg_setReg_eq (by decide)]
  rfl

theorem outside_index_work_low (a : Word) (low : a.toNat < 0x80000) : OutsideIndexWork a := by
  refine ⟨?_,?_,?_⟩
  all_goals
    intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    have := i.isLt
    omega

/-- Exact organizer-loaded signer prefix, universally including arbitrary untrusted caches. -/
theorem loaded_loop_entry (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) :
    ∃ initial final,
      initialState submission .sign (secretKey,pk,cache,message) = some initial ∧
      Trace hash sign initial 226 256 2 4 final ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)).zeroExtend 192) ∧
      final.getReg .x2 = 0x1000000 ∧ final.getMem 0x80400 = 0 ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧
      final.getMem 0x80500 = 0 ∧ final.getMem 0x80508 = 0 ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      (∀ a, a.toNat < 0x80000 → (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        final.getMem a = initial.getMem a) := by
  obtain ⟨initial,loaded,pc⟩ := initialState_exists submission admitted .sign (secretKey,pk,cache,message)
  obtain ⟨final,run,fpc,index,randomizer,mode,pointer,sp,frame⟩ := entry_full hash initial secretKey pk message pc
    (Loader.sign_secretKey submission (admitted.2 .sign) secretKey pk cache message initial loaded)
    (Loader.sign_publicKey submission (admitted.2 .sign) secretKey pk cache message initial loaded)
    (Loader.sign_message submission (admitted.2 .sign) secretKey pk cache message initial loaded)
  refine ⟨initial,final,loaded,run,fpc,index,sp.trans (loaded_stack secretKey pk cache message initial loaded),?_,mode,pointer,?_,?_,randomizer,?_⟩
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey pk cache message initial loaded _ (by decide)
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey pk cache message initial loaded _ (by decide)
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey pk cache message initial loaded _ (by decide)
  · intro a low outside
    apply frame a ⟨outside_index_work_low a low,outside,?_,?_⟩
    · intro eq; rw [eq] at low; change 0x80440 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80448 < 0x80000 at low; omega

/-- info: 'SigGolfCandidate.Hypertree.Signing.loaded_loop_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_loop_entry

end SigGolfCandidate.Hypertree.Signing
