import SigGolfCandidate.Hypertree.PreludeLoadedPrepared
import SigGolfCandidate.Hypertree.PreludePrefixRefine
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

theorem digest_bytes (s : MachineState) (value : Reference.Digest)
    (words : ∀ i : Fin 2, s.getMem (wordAddress 0x40 i.val) = value.extractLsb' (64*i.val) 64)
    (i : Nat) (hi : i < 16) :
    s.getByte (BitVec.ofNat 64 (0x40+i)) = value.extractLsb' (8*i) 8 := by
  rw [getByte_word s 0x40 i (by decide) (by omega), words ⟨i/8, by omega⟩]
  ext j hj
  have hb : i % 8 * 8 + j < 64 := by omega
  have he : 64 * (i / 8) + (i % 8 * 8 + j) = 8 * i + j := by omega
  simp [extractByte, hb, he]

theorem loaded_prefix (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s) :
    ∃ final instructions cycles, Trace hash signPrelude s instructions cycles 741 765 final ∧
      instructions ≤ 100659 ∧ cycles ≤ 106038 ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash (Reference.keygen hash secretKey) message
        (Reference.randomizer hash secretKey message)).zeroExtend 192) ∧
      final.getReg .x2 = 0x1000000 ∧ final.getMem 0x80400 = 0 ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) = 0) ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64) := by
  obtain ⟨prepared,n,c,pre,nb,cb,pc,sp,entryReady,pk,level,idx,current,frame⟩ :=
    loaded_prepared hash secretKey cache message s loaded
  have inputBytes (base i : Nat) (align : base%8=0) (bound : base+i<64) :
      prepared.getByte (BitVec.ofNat 64 (base+i)) = s.getByte (BitVec.ofNat 64 (base+i)) := by
    rw [getByte_word prepared base i align (by omega), getByte_word s base i align (by omega)]
    change extractByte (prepared.getMem (BitVec.ofNat 64 (base+8*(i/8)))) _ = _
    rw [frame _ (by omega) (by omega) (by omega) (by omega)]
    rfl
  have skBytes := Loader.sign_secretKey preludeSubmission sign_valid (by rfl) secretKey cache message s loaded
  have msgBytes := Loader.sign_message preludeSubmission sign_valid (by rfl) secretKey cache message s loaded
  have sk : ∀ i, i<32 → prepared.getByte (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8 := by
    intro i hi; rw [inputBytes 0x20 i (by decide) (by omega)]; exact skBytes i hi
  have msg : ∀ i, i<32 → prepared.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8 := by
    intro i hi
    have eq := inputBytes 0 i (by decide) (by omega)
    simp only [Nat.zero_add] at eq
    rw [eq]; exact msgBytes i hi
  obtain ⟨final,run,fpc,index,randomizer,mode,pointer,fsp,keep⟩ :=
    entry_full hash prepared secretKey (Reference.keygen hash secretKey) message pc entryReady sk
      (digest_bytes prepared _ pk) msg
  refine ⟨final,n+237,c+267,pre.trans run,by omega,by omega,fpc,index,fsp.trans sp,?_,mode,pointer,?_,randomizer,?_,?_⟩
  · rw [keep _ (by unfold OutsidePrefix OutsideIndexWork; decide)]; exact level
  · intro i
    rw [keep _ (by unfold OutsidePrefix OutsideIndexWork; fin_cases i <;> decide)]; exact current i
  · intro i
    rw [keep _ (by unfold OutsidePrefix OutsideIndexWork; fin_cases i <;> decide)]; exact pk i
  · intro i
    rw [keep _ (by unfold OutsidePrefix OutsideIndexWork; fin_cases i <;> decide)]
    have h := frame (0x20+8*i.val) (by omega) (by have := i.isLt; omega)
      (by have := i.isLt; omega) (by have := i.isLt; omega)
    rw [show wordAddress 0x20 i.val = BitVec.ofNat 64 (0x20+8*i.val) from rfl,h]
    exact loaded_secret_words secretKey cache message s loaded i

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.loaded_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_prefix
end SigGolfCandidate.Hypertree.Signing.Prelude
