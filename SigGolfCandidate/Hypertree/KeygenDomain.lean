import SigGolfCandidate.Hypertree.KeygenNode

namespace SigGolfCandidate.Hypertree.KeygenDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def header (tag level leaf chain step : Nat) : Word :=
  BitVec.ofNat 64 (tag + level * 2^8 + leaf * 2^16 + chain * 2^24 + step * 2^32)

theorem header_zero (tag level leaf chain : Nat) :
    header tag level leaf chain 0 = BitVec.ofNat 64 (tag + level * 2^8 + leaf * 2^16 + chain * 2^24) := by
  unfold header
  rw [Nat.zero_mul,Nat.add_zero]

def inputWord (head : Word) (tree : Nat) (value : Reference.Digest) (i : Fin 6) : Word :=
  if i.val = 0 then head
  else if i.val < 4 then (BitVec.ofNat 192 tree).extractLsb' (64 * (i.val-1)) 64
  else value.extractLsb' (64 * (i.val-4)) 64

def payload (head : Word) (tree : Nat) (value : Reference.Digest) : List Byte :=
  bytes (n := 8) head ++ bytes (n := 24) (BitVec.ofNat 192 tree) ++ bytes value

@[simp] theorem payload_length (head : Word) (tree : Nat) (value : Reference.Digest) :
    (payload head tree value).length = 48 := by simp [payload,bytes]

theorem payload_byte (head : Word) (tree : Nat) (value : Reference.Digest) (i : Fin 48) :
    extractByte (inputWord head tree value ⟨i.val/8,by have := i.isLt; omega⟩) (i.val%8) =
      (payload head tree value)[i.val]'(by simp) := by
  fin_cases i <;> simp [inputWord,payload,bytes,List.getElem_append]
  all_goals
    ext j hj
    interval_cases j <;> simp [extractByte,← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat]

theorem query_eq (s : MachineState) (head : Word) (tree : Nat) (value : Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 384)
    (words : ∀ i : Fin 6, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord head tree value i) :
    hashInput s = Reference.packed (payload head tree value) := by
  apply Serialization.hashInput_of_list s 0x80000 (payload head tree value)
  · exact source
  · rw [bits,payload_length]; rfl
  · intro i hi
    have bound : i < 48 := by simpa using hi
    rw [Signing.getByte_word s 0x80000 i (by decide) (by omega),words ⟨i/8,by omega⟩]
    exact payload_byte head tree value ⟨i,bound⟩

theorem answer_words (hash : Hash) (s : MachineState)
    (tag level tree leaf chain step : Nat) (value : Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 6, s.getMem (Signing.wordAddress 0x80000 i.val) =
      inputWord (header tag level leaf chain step) tree value i) :
    ∀ i : Fin 2, (writeHash s (hash (hashInput s))).getMem (Signing.wordAddress 0x80300 i.val) =
      (Reference.truncate (Reference.query hash tag level tree leaf chain step (bytes value))).extractLsb' (64*i.val) 64 := by
  intro i
  rw [Signing.hash_answer_word s (hash (hashInput s)) destination ⟨i.val,by have := i.isLt; omega⟩]
  have eq : hash (hashInput s) = Reference.query hash tag level tree leaf chain step (bytes value) := by
    rw [query_eq s _ tree value source bits words]
    rfl
  rw [eq]
  let result := Reference.query hash tag level tree leaf chain step (bytes value)
  change result.extractLsb' (64*i.val) 64 = (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem hash_trace (image : Image) (hash : Hash) (s : MachineState)
    (code : fetch image s = some (.base .ECALL)) (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80300) :
    Trace hash image s 1 8 1 1 (writeHash s (hash (hashInput s))) := by
  have valid := Keygen.hash_arguments s 384 source bits destination (by decide)
  have len : (hashInput s).1 = 384 := by simp [hashInput,bits]
  simpa [len,compressions] using
    Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

/-- Natural domain fields are accumulated modulo 2^64 exactly as in the reference header. -/
theorem shift_ofNat (n k : Nat) :
    (BitVec.ofNat 64 n <<< k) = BitVec.ofNat 64 (n * 2^k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have two : BitVec.twoPow 64 k = BitVec.ofNat 64 (2^k) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
  rw [two,← BitVec.ofNat_mul]

/-- Six concrete memory words determine the complete 48-byte query. -/
theorem words_of_layout (s : MachineState) (head : Word) (tree : Nat) (value : Reference.Digest)
    (hhead : s.getMem 0x80000 = head)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80008 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 6, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord head tree value i := by
  have h0 := hindex 0
  have h1 := hindex 1
  have h2 := hindex 2
  have v0 := hvalue 0
  have v1 := hvalue 1
  norm_num [Signing.wordAddress] at h0 h1 h2 v0 v1
  intro i
  fin_cases i <;> simp only [Signing.wordAddress,inputWord,Fin.reduceFinMk] <;> norm_num
  · exact hhead
  · exact h0
  · exact h1
  · exact h2
  · exact v0
  · exact v1

end SigGolfCandidate.Hypertree.KeygenDomain
