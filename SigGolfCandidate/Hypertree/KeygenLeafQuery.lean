import SigGolfCandidate.Hypertree.KeygenDomain
import Mathlib.Data.List.OfFn

namespace SigGolfCandidate.Hypertree.KeygenLeaf
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096

theorem bytes_ofFn (value : Reference.Digest) :
    bytes value = List.ofFn (fun i : Fin 16 => value.extractLsb' (8*i.val) 8) := by
  apply List.ext_getElem
  · simp [bytes]
  · intro i hi hj
    simp only [bytes,List.getElem_map,List.getElem_range,List.getElem_ofFn]

def endpointBytes (values : Reference.Chain → Reference.Digest) : List Byte :=
  List.ofFn (fun i : Fin (46*16) =>
    (values ⟨i.val/16,by have := i.isLt; omega⟩).extractLsb' (8*(i.val%16)) 8)

theorem endpoints_eq (values : Reference.Chain → Reference.Digest) :
    ((List.ofFn values).flatMap fun value => bytes value) = endpointBytes values := by
  unfold endpointBytes
  rw [List.ofFn_mul (m:=46) (n:=16)]
  simp only [List.flatMap, List.map_ofFn, bytes_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have div : (i.val*16+j.val)/16 = i.val := by omega
  have mod : (i.val*16+j.val)%16 = j.val := by omega
  simp only [div,mod]

def payload (head : Word) (tree : Nat) (values : Reference.Chain → Reference.Digest) : List Byte :=
  bytes (n:=8) head ++ bytes (n:=24) (BitVec.ofNat 192 tree) ++ endpointBytes values

@[simp] theorem payload_length (head : Word) (tree : Nat) (values : Reference.Chain → Reference.Digest) :
    (payload head tree values).length = 768 := by
  simp only [payload,List.length_append,bytes,List.length_map,List.length_range,endpointBytes,List.length_ofFn]

def inputWord (head : Word) (tree : Nat) (values : Reference.Chain → Reference.Digest) (i : Fin 96) : Word :=
  if i.val=0 then head else if i.val<4 then
    (BitVec.ofNat 192 tree).extractLsb' (64*(i.val-1)) 64 else
    (values ⟨(i.val-4)/2,by have := i.isLt; omega⟩).extractLsb' (64*((i.val-4)%2)) 64

theorem payload_byte (head : Word) (tree : Nat) (values : Reference.Chain → Reference.Digest) (i : Fin 768) :
    extractByte (inputWord head tree values ⟨i.val/8,by have := i.isLt; omega⟩) (i.val%8) =
      (payload head tree values)[i.val]'(by simp) := by
  by_cases first : i.val < 32
  · obtain ⟨i,hi⟩ := i
    dsimp at first
    interval_cases i <;> simp [inputWord,payload,bytes]
    all_goals
      ext j hj
      interval_cases j <;> simp [extractByte,← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat]
  · have big : 32 ≤ i.val := by omega
    have q0 : ¬ i.val/8=0 := by omega
    have q4 : ¬ i.val/8<4 := by omega
    have offset : i.val-32 < 736 := by have := i.isLt; omega
    have div : (i.val/8-4)/2 = (i.val-32)/16 := by omega
    have shift : 64*((i.val/8-4)%2) + (i.val%8*8) = 8*((i.val-32)%16) := by omega
    simp only [inputWord,q0,q4,↓reduceIte,payload,List.getElem_append,bytes,List.length_map,List.length_range,List.length_append]
    simp only [show ¬ i.val<8+24 from by omega,↓reduceDIte,endpointBytes,List.getElem_ofFn]
    simp only [div]
    ext j hj
    have low : i.val%8*8+j < 64 := by omega
    simp [extractByte,low,← Nat.add_assoc,shift]

theorem query_eq (s : MachineState) (head : Word) (tree : Nat) (values : Reference.Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 6144)
    (words : ∀ i : Fin 96, s.getMem (Signing.wordAddress 0x80000 i.val) = inputWord head tree values i) :
    hashInput s = Reference.packed (payload head tree values) := by
  apply Serialization.hashInput_of_list s 0x80000 (payload head tree values)
  · exact source
  · rw [bits,payload_length]; rfl
  · intro i hi
    have bound : i < 768 := by simpa using hi
    rw [Signing.getByte_word s 0x80000 i (by decide) (by omega),words ⟨i/8,by omega⟩]
    exact payload_byte head tree values ⟨i,bound⟩

/-- The exact 768-byte endpoint-compression query returns the reference leaf root. -/
theorem answer_words (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (values : Reference.Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 6144)
    (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 96, s.getMem (Signing.wordAddress 0x80000 i.val) =
      inputWord (BitVec.ofNat 64 (3 + level*2^8 + Reference.sideNumber side*2^16)) tree values i) :
    ∀ i : Fin 2, (writeHash s (hash (hashInput s))).getMem (Signing.wordAddress 0x80300 i.val) =
      (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64 := by
  intro i
  rw [Signing.hash_answer_word s (hash (hashInput s)) destination ⟨i.val,by have := i.isLt; omega⟩]
  have query := query_eq s _ tree values source bits words
  have answer : Reference.compressLeaf hash level tree side values = Reference.truncate (hash (hashInput s)) := by
    rw [query]
    simp only [Reference.compressLeaf,Reference.query,payload]
    have arithmetic : 3 + level*2^8 + Reference.sideNumber side*2^16 + 0*2^24 + 0*2^32 =
        3 + level*2^8 + Reference.sideNumber side*2^16 := by simp only [Nat.zero_mul,Nat.add_zero]
    rw [arithmetic,endpoints_eq]
  rw [answer]
  change (hash (hashInput s)).extractLsb' (64*i.val) 64 =
    ((hash (hashInput s)).extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem hash_trace (image : Image) (hash : Hash) (s : MachineState)
    (code : fetch image s = some (.base .ECALL)) (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000) (bits : s.getReg .x11 = 6144)
    (destination : s.getReg .x12 = 0x80300) :
    Trace hash image s 1 96 1 12 (writeHash s (hash (hashInput s))) := by
  have valid := Keygen.hash_arguments s 6144 source bits destination (by decide)
  have len : (hashInput s).1 = 6144 := by simp [hashInput,bits]
  simpa [len,compressions] using Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeaf.answer_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms answer_words

end SigGolfCandidate.Hypertree.KeygenLeaf
