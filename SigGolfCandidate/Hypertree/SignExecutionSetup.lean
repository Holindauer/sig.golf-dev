import SigGolfCandidate.Hypertree.SignLayers
import SigGolfCandidate.Hypertree.SignLoopEntry

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

theorem digest_words_of_bytes (s : MachineState) (base : Nat) (value : Reference.Digest)
    (aligned : base%8=0) (bound : base+16<2^64)
    (bytes : ∀ i, i<16 → s.getByte (BitVec.ofNat 64 (base+i)) = value.extractLsb' (8*i) 8)
    (i : Fin 2) : s.getMem (wordAddress base i.val)=value.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<16 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := bytes (8*i.val+j) whole
  rw [getByte_word _ base (8*i.val+j) aligned (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice value (8*i.val+j)

theorem secretKey_words_of_bytes (s : MachineState) (base : Nat) (value : SecretKey)
    (aligned : base%8=0) (bound : base+32<2^64)
    (bytes : ∀ i, i<32 → s.getByte (BitVec.ofNat 64 (base+i)) = value.extractLsb' (8*i) 8)
    (i : Fin 4) : s.getMem (wordAddress base i.val)=value.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<32 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := bytes (8*i.val+j) whole
  rw [getByte_word _ base (8*i.val+j) aligned (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice value (8*i.val+j)

theorem digest_eq_of_words (left right : Reference.Digest)
    (words : ∀ i : Fin 2, left.extractLsb' (64*i.val) 64=right.extractLsb' (64*i.val) 64) : left=right := by
  have lo := congrArg BitVec.toNat (words 0)
  have hi := congrArg BitVec.toNat (words 1)
  have lb := left.isLt; have rb := right.isLt
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow] at lo hi
  omega

/-- The official loaded prefix satisfies every hypothesis of the complete loop. -/
theorem loaded_loop_data (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) :
    ∃ initial ready, initialState submission .sign (secretKey,pk,cache,message)=some initial ∧
      Trace hash sign initial 238 268 2 4 ready ∧ ready.pc=0x1220 ∧
      LoopData ready secretKey 0 (Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)).toNat 0 ∧
      (∀ i : Fin 4, ready.getMem (wordAddress 0x20060 i.val)=
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2, ready.getMem (wordAddress 0x40 i.val)=pk.extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,ready,loaded,run,pc,index,sp,level,mode,ptr,lo,hi,randomizer,frame⟩ :=
    loaded_loop_entry hash secretKey pk cache message
  have loadedSecretKey := secretKey_words_of_bytes initial 0x20 secretKey (by decide) (by decide)
    (Loader.sign_secretKey submission (admitted.2 .sign) (by rfl) secretKey pk cache message initial loaded)
  have loadedPk := digest_words_of_bytes initial 0x40 pk (by decide) (by decide)
    (Loader.sign_publicKey submission (admitted.2 .sign) (by rfl) secretKey pk cache message initial loaded)
  refine ⟨initial,ready,loaded,run,pc,?_,randomizer,?_⟩
  · constructor
    · exact sp
    · exact level
    · have eq : (Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)).zeroExtend 192 =
          BitVec.ofNat 192 (Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)).toNat := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [←eq]; exact index
    · intro i
      rw [frame _ (by fin_cases i <;> decide) (by intro j; fin_cases i <;> fin_cases j <;> decide)]
      exact loadedSecretKey i
    · exact mode
    · exact ptr
    · intro i
      fin_cases i
      · exact lo
      · exact hi
  · intro i
    rw [frame _ (by fin_cases i <;> decide) (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact loadedPk i

end SigGolfCandidate.Hypertree.Signing
