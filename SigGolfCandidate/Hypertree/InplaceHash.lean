import SigGolfCandidate.Hypertree.KeygenDomain
namespace SigGolfCandidate.Hypertree.InplaceHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing

theorem answer_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (i : Fin 4) :
    (writeHash s answer).getMem (wordAddress 0x80020 i.val) =
      answer.extractLsb' (64 * i.val) 64 := by
  fin_cases i <;> simp [writeHash, dst, wordAddress, MachineState.writeWords, Expansion.mem_setMem]

theorem header_preserved (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (i : Fin 4) :
    (writeHash s answer).getMem (wordAddress 0x80000 i.val) =
      s.getMem (wordAddress 0x80000 i.val) := by
  fin_cases i <;> simp [writeHash, dst, wordAddress, MachineState.writeWords, Expansion.mem_setMem]

theorem hash_trace (image : Image) (hash : Hash) (s : MachineState)
    (code : fetch image s = some (.base .ECALL)) (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 48)
    (destination : s.getReg .x12 = 0x80020) :
    Trace hash image s 1 8 1 1 (writeHash s (hash (hashInput s))) := by
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid, source, bits, destination, rangeValid, accessValid, MEMORY_BYTES]
  have len : (hashInput s).1 = 384 := by simp [hashInput,bits]
  simpa [len,compressions] using
    Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

/-- info: 'SigGolfCandidate.Hypertree.InplaceHash.answer_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms answer_word
/-- info: 'SigGolfCandidate.Hypertree.InplaceHash.header_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms header_preserved
/-- info: 'SigGolfCandidate.Hypertree.InplaceHash.hash_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hash_trace
theorem frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80020 := outside 0
  have h1 : a ≠ 0x80028 := outside 1
  have h2 : a ≠ 0x80030 := outside 2
  have h3 : a ≠ 0x80038 := outside 3
  simp only [writeHash, MachineState.getMem_setPC, dst, MachineState.writeWords,
    Expansion.mem_setMem]
  change (if a = 0x80038 then _ else if a = 0x80030 then _ else
    if a = 0x80028 then _ else if a = 0x80020 then _ else s.getMem a) = s.getMem a
  rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0]


open KeygenDomain

theorem answer_words (hash : Hash) (s : MachineState)
    (tag level tree leaf chain step : Nat) (value : Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 48)
    (destination : s.getReg .x12 = 0x80020)
    (words : ∀ i : Fin 6, s.getMem (Signing.wordAddress 0x80000 i.val) =
      inputWord (header tag level leaf chain step) tree value i) :
    ∀ i : Fin 2, (writeHash s (hash (hashInput s))).getMem (Signing.wordAddress 0x80020 i.val) =
      (Reference.truncate (Reference.query hash tag level tree leaf chain step (bytes value))).extractLsb' (64*i.val) 64 := by
  intro i
  rw [answer_word s (hash (hashInput s)) destination ⟨i.val,by have := i.isLt; omega⟩]
  have eq : hash (hashInput s) = Reference.query hash tag level tree leaf chain step (bytes value) := by
    rw [query_eq s _ tree value source bits words]
    rfl
  rw [eq]
  let result := Reference.query hash tag level tree leaf chain step (bytes value)
  change result.extractLsb' (64*i.val) 64 = (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

/-- info: 'SigGolfCandidate.Hypertree.InplaceHash.answer_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms answer_words
end SigGolfCandidate.Hypertree.InplaceHash
