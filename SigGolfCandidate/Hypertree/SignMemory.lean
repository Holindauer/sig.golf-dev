import SigGolfCandidate.Hypertree.SignPrepare
import RiscvZkvm.Rv64.Logic.MemRegion

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- The byte view of an aligned word buffer, using the actual machine memory model. -/
theorem getByte_word (s : MachineState) (base i : Nat)
    (aligned : base % 8 = 0) (bound : base + i < 2 ^ 64) :
    s.getByte (BitVec.ofNat 64 (base + i)) =
      extractByte (s.getMem (wordAddress base (i / 8))) (i % 8) := by
  have hb : base < 2 ^ 64 := by omega
  have ha : (BitVec.ofNat 64 base).toNat % 8 = 0 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using aligned
  have hi : (BitVec.ofNat 64 base).toNat + i < 2 ^ 64 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using bound
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned ha hi,
    byteOffset_add_ofNat_of_aligned ha hi, wordAddress]

/-- Word equality implies byte equality, including a partial last word. -/
theorem bytes_eq_of_words (original final : MachineState) (source destination count : Nat)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (srcbound : source + count ≤ 2 ^ 64) (dstbound : destination + count ≤ 2 ^ 64)
    (words : ∀ j, j < (count + 7) / 8 →
      final.getMem (wordAddress destination j) = original.getMem (wordAddress source j))
    (i : Nat) (hi : i < count) :
    final.getByte (BitVec.ofNat 64 (destination + i)) =
      original.getByte (BitVec.ofNat 64 (source + i)) := by
  rw [getByte_word final destination i dstalign (by omega),
    getByte_word original source i srcalign (by omega), words (i / 8) (by omega)]

/-- Exact byte form of the prepared tag6/secret key/message buffer. -/
def randomizerInputByte (s : MachineState) (i : Fin 96) : Byte :=
  extractByte (randomizerInputWord s ⟨i.val / 8, by have := i.isLt; omega⟩) (i.val % 8)

theorem prepared_randomizer_bytes (original ready : MachineState)
    (words : ∀ i : Fin 12, ready.getMem (wordAddress 0x80000 i.val) = randomizerInputWord original i)
    (i : Fin 96) :
    ready.getByte (BitVec.ofNat 64 (0x80000 + i.val)) = randomizerInputByte original i := by
  rw [getByte_word ready 0x80000 i.val (by decide) (by have := i.isLt; omega)]
  exact congrArg (fun word => extractByte word (i.val % 8))
    (words ⟨i.val / 8, by have := i.isLt; omega⟩)

/-- Every byte of a checked copy loop is transferred, even if only a prefix of the
last word is relevant to the caller's serialized buffer. -/
theorem copy_bytes_of_content (source destination total : Nat) (original final : MachineState)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (content : CopyContent source destination total 0 original final)
    (i : Nat) (hi : i < 8 * total) :
    final.getByte (BitVec.ofNat 64 (destination + i)) =
      original.getByte (BitVec.ofNat 64 (source + i)) := by
  apply bytes_eq_of_words original final source destination (8 * total) srcalign dstalign
  · simp only [MEMORY_BYTES] at srcbound; omega
  · simp only [MEMORY_BYTES] at dstbound; omega
  · intro j hj
    exact content.2 j (by omega)
  · exact hi

/-- info: 'SigGolfCandidate.Hypertree.Signing.bytes_eq_of_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytes_eq_of_words

/-- The prepared bytes are exactly the domain header followed by secret key and message. -/
theorem randomizerInputByte_spec (s : MachineState) (i : Fin 96) :
    randomizerInputByte s i =
      if i.val = 0 then 6 else if i.val < 32 then 0 else
        if i.val < 64 then s.getByte (BitVec.ofNat 64 (0x20 + (i.val - 32)))
        else s.getByte (BitVec.ofNat 64 (i.val - 64)) := by
  fin_cases i <;> first | rfl | simp [randomizerInputByte, randomizerInputWord, extractByte]

/-- Extracting a byte from a stored 64-bit slice agrees with direct byte extraction. -/
theorem extractByte_slice (value : BitVec 256) (i : Fin 32) :
    extractByte (value.extractLsb' (64 * (i.val / 8)) 64) (i.val % 8) =
      value.extractLsb' (8 * i.val) 8 := by
  ext j hj
  have hb : i.val % 8 * 8 + j < 64 := by omega
  have he : 64 * (i.val / 8) + (i.val % 8 * 8 + j) = 8 * i.val + j := by omega
  simp [extractByte, hb, he]

/-- Four consecutive answer words encode the complete 256-bit value. -/
theorem bytes_of_answer_words (s : MachineState) (base : Nat) (answer : BitVec 256)
    (align : base % 8 = 0) (bound : base + 32 ≤ 2 ^ 64)
    (words : ∀ i : Fin 4, s.getMem (wordAddress base i.val) = answer.extractLsb' (64 * i.val) 64)
    (i : Nat) (hi : i < 32) :
    s.getByte (BitVec.ofNat 64 (base + i)) = answer.extractLsb' (8 * i) 8 := by
  rw [getByte_word s base i align (by omega), words ⟨i / 8, by omega⟩]
  exact extractByte_slice answer ⟨i, hi⟩

end SigGolfCandidate.Hypertree.Signing
