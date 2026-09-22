import SigGolfCandidate.Hypertree.SignMemory
import SigGolfCandidate.Serialization

namespace SigGolfCandidate.Hypertree.KeygenNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Word form of the 64-byte tree-node query used by every image. -/
def inputWord (level tree : Nat) (left right : Reference.Digest) (i : Fin 8) : Word :=
  if i.val = 0 then BitVec.ofNat 64 (4 + level * 2 ^ 8)
  else if i.val < 4 then (BitVec.ofNat 192 tree).extractLsb' (64 * (i.val - 1)) 64
  else if i.val < 6 then left.extractLsb' (64 * (i.val - 4)) 64
  else right.extractLsb' (64 * (i.val - 6)) 64

def payload (level tree : Nat) (left right : Reference.Digest) : List Byte :=
  bytes (n := 8) (BitVec.ofNat 64 (4 + level * 2 ^ 8)) ++
    bytes (n := 24) (BitVec.ofNat 192 tree) ++ (bytes left ++ bytes right)

@[simp] theorem payload_length (level tree : Nat) (left right : Reference.Digest) :
    (payload level tree left right).length = 64 := by simp [payload, bytes]

theorem extractByte_slice {n : Nat} (value : BitVec n) (i : Nat) :
    extractByte (value.extractLsb' (64 * (i / 8)) 64) (i % 8) =
      value.extractLsb' (8 * i) 8 := by
  ext j hj
  have hb : i % 8 * 8 + j < 64 := by omega
  have he : 64 * (i / 8) + (i % 8 * 8 + j) = 8 * i + j := by omega
  simp [extractByte, hb, he]

theorem payload_byte (level tree : Nat) (left right : Reference.Digest) (i : Fin 64) :
    extractByte (inputWord level tree left right ⟨i.val / 8, by have := i.isLt; omega⟩) (i.val % 8) =
      (payload level tree left right)[i.val]'(by simp) := by
  fin_cases i <;> simp [inputWord, payload, bytes, List.getElem_append]
  all_goals
    ext j hj
    interval_cases j <;> simp [extractByte, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]

/-- A word-level subroutine invariant establishes the precise reference oracle input. -/
theorem query_eq (s : MachineState) (level tree : Nat) (left right : Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 512)
    (words : ∀ i : Fin 8, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord level tree left right i) :
    hashInput s = Reference.packed (payload level tree left right) := by
  apply Serialization.hashInput_of_list s 0x80000 (payload level tree left right)
  · exact source
  · rw [bits, payload_length]; rfl
  · intro i hi
    have bound : i < 64 := by simpa using hi
    rw [Signing.getByte_word s 0x80000 i (by decide) (by omega), words ⟨i / 8, by omega⟩]
    exact payload_byte level tree left right ⟨i, bound⟩

/-- The concrete HASH write contains the reference node digest. -/
theorem node_answer (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 512)
    (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 8, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord level tree left right i) :
    ∀ i : Fin 2, (writeHash s (hash (hashInput s))).getMem (Signing.wordAddress 0x80300 i.val) =
      (Reference.node hash level tree left right).extractLsb' (64 * i.val) 64 := by
  intro i
  rw [Signing.hash_answer_word s (hash (hashInput s)) destination ⟨i.val, by have := i.isLt; omega⟩]
  have query := query_eq s level tree left right source bits words
  have node_eq : Reference.node hash level tree left right = Reference.truncate (hash (hashInput s)) := by
    rw [query]
    simp only [Reference.node, Reference.query, payload]
    have arithmetic : 4 + level * 2 ^ 8 + 0 * 2 ^ 16 + 0 * 2 ^ 24 + 0 * 2 ^ 32 =
        4 + level * 2 ^ 8 := by simp only [Nat.zero_mul, Nat.add_zero]
    rw [arithmetic]
  rw [node_eq]
  change (hash (hashInput s)).extractLsb' (64 * i.val) 64 =
    ((hash (hashInput s)).extractLsb' 0 128).extractLsb' (64 * i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)


/-- A prepared node HASH executes exactly once and returns the reference node answer. -/
theorem hashes_node (image : Image) (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (code : fetch image s = some (.base .ECALL))
    (service : s.getReg .x5 = 1) (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 512) (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 8, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord level tree left right i) :
    ∃ final, Trace hash image s 1 8 1 1 final ∧ final.pc = s.pc + 4 ∧
      ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80300 i.val) =
        (Reference.node hash level tree left right).extractLsb' (64 * i.val) 64 := by
  let answer := hash (hashInput s)
  have valid := Keygen.hash_arguments s 512 source bits destination (by decide)
  have len : (hashInput s).1 = 512 := by simp [hashInput, bits]
  refine ⟨writeHash s answer, ?_, Keygen.hash_pc _ _, ?_⟩
  · simpa [len, compressions] using
      Trace.hash s (writeHash s answer) 0 0 0 0 code service valid (Trace.refl _)
  · exact node_answer hash s level tree left right source bits destination words

/-- The node HASH site in the exact keygen image. -/
theorem keygen_hash_site (s : MachineState) (pc : s.pc = 0x1190) :
    fetch keygen s = some (.base .ECALL) := by
  simp only [fetch, pc, keygen]
  decide

/-- info: 'SigGolfCandidate.Hypertree.KeygenNode.hashes_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hashes_node

end SigGolfCandidate.Hypertree.KeygenNode
