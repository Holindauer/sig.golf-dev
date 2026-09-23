import SigGolfCandidate.Hypertree.VerifyWireLayers
import SigGolfCandidate.Hypertree.VerifyLoopEntry

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem loaded_publicKey_word (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s) (i : Fin 2) :
    s.getMem (wordAddress 0x40 i.val) = pk.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have quot : (8*i.val+j)/8 = i.val := by omega
  have rem : (8*i.val+j)%8 = j := by omega
  have h := loaded_publicKey pk message witness s loaded (8*i.val+j) (by omega)
  rw [getByte_word s 0x40 (8*i.val+j) (by decide) (by omega)] at h
  simp only [quot, rem] at h
  rw [h]
  symm
  simpa only [quot, rem] using KeygenNode.extractByte_slice pk (8*i.val+j)

/-- The organizer's loader and index prefix establish the full loop invariant. -/
theorem loaded_loop_data (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial ready, initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial 130 145 1 2 ready ∧ ready.pc = 0x1148 ∧
      LoopData ready 0 (Reference.indexOf hash pk message (SignatureEncoding.decode witness).randomizer).toNat 0 witness ∧
      LowFrame initial ready := by
  obtain ⟨initial, ready, loaded, run, pc, index, sp, level, _, pointer, current0, current1, frame⟩ :=
    loaded_loop_entry hash pk message witness
  have lowFrame : LowFrame initial ready := by
    intro address _ bound
    exact frame _ (by change address % 2^64 < 0x80000; omega)
  refine ⟨initial, ready, loaded, run, pc, ?_, lowFrame⟩
  refine ⟨sp, level, ?_, pointer, ?_, ?_⟩
  · have cast (value : BitVec 152) : value.zeroExtend 192 = BitVec.ofNat 192 value.toNat := by
      apply BitVec.eq_of_toNat_eq
      simp
    rw [cast] at index
    exact index
  · intro i
    fin_cases i
    · exact current0
    · exact current1
  · exact (WitnessStored.loaded pk message witness initial loaded).transfer_words initial ready witness lowFrame

theorem digest_eq_of_words (left right : Reference.Digest)
    (words : ∀ i : Fin 2, left.extractLsb' (64*i.val) 64 = right.extractLsb' (64*i.val) 64) : left = right := by
  ext j hj
  simp only [← BitVec.getLsbD_eq_getElem]
  by_cases low : j < 64
  · have h := congrArg (fun value : BitVec 64 => value.getLsbD j) (words 0)
    simpa [low] using h
  · have pos : j-64 < 64 := by omega
    have eq : 64+(j-64) = j := by omega
    have h := congrArg (fun value : BitVec 64 => value.getLsbD (j-64)) (words 1)
    simpa [pos, eq] using h

theorem root_matches_iff (s : MachineState) (root pk : Reference.Digest)
    (current : ∀ i : Fin 2, s.getMem (wordAddress 0x80500 i.val) = root.extractLsb' (64*i.val) 64)
    (publicKey : ∀ i : Fin 2, s.getMem (wordAddress 0x40 i.val) = pk.extractLsb' (64*i.val) 64) :
    RootMatches s ↔ root = pk := by
  have c0 : s.getMem 0x80500 = root.extractLsb' 0 64 := current 0
  have c1 : s.getMem 0x80508 = root.extractLsb' 64 64 := current 1
  have p0 : s.getMem 0x40 = pk.extractLsb' 0 64 := publicKey 0
  have p1 : s.getMem 0x48 = pk.extractLsb' 64 64 := publicKey 1
  unfold RootMatches
  rw [c0, c1, p0, p1]
  constructor
  · intro h
    apply digest_eq_of_words
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  · intro h; rw [h]; exact ⟨rfl, rfl⟩

end SigGolfCandidate.Hypertree.Verifying
