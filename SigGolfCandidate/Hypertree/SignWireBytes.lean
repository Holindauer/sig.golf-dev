import SigGolfCandidate.Hypertree.SignLayersMemory
import SigGolfCandidate.Hypertree.Signature

namespace SigGolfCandidate.Hypertree.SignWire
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Signing SignatureEncoding
set_option maxRecDepth 4096

def StoredBytes (s : MachineState) (base : Nat) (data : List Byte) : Prop :=
  ∀ i (hi : i < data.length), s.getByte (BitVec.ofNat 64 (base+i)) = data[i]

theorem StoredBytes.append (s : MachineState) (base : Nat) (first second : List Byte)
    (left : StoredBytes s base first) (right : StoredBytes s (base+first.length) second) :
    StoredBytes s base (first++second) := by
  intro i hi
  by_cases lt : i < first.length
  · rw [List.getElem_append_left lt]
    exact left i lt
  · have hb : i-first.length < second.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right (by omega)]
    have eq := right (i-first.length) hb
    simpa only [show base+first.length+(i-first.length)=base+i by omega] using eq

theorem words_bytes {n : Nat} (s : MachineState) (base : Nat) (value : Bytes n)
    (aligned : base%8=0) (bound : base+n < 2^64)
    (words : ∀ i, i < (n+7)/8 → s.getMem (wordAddress base i) = value.extractLsb' (64*i) 64) :
    StoredBytes s base (bytes value) := by
  intro i hi
  have hn : i < n := by simpa only [Memory.bytes_length] using hi
  rw [getByte_word s base i aligned (by omega),words (i/8) (by omega)]
  simpa only [bytes,List.getElem_map,List.getElem_range] using KeygenNode.extractByte_slice value i

theorem digest_bytes (s : MachineState) (base : Nat) (value : Reference.Digest)
    (aligned : base%8=0) (bound : base+16 < 2^64)
    (words : ∀ i : Fin 2, s.getMem (wordAddress base i.val) = value.extractLsb' (64*i.val) 64) :
    StoredBytes s base (bytes value) :=
  words_bytes s base value aligned bound (fun i hi => words ⟨i,hi⟩)

theorem captured_bytes (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (value : Reference.Digest)
    (aligned : pointer%8=0) (bound : pointer+752 < 2^64)
    (stored : CapturedValue s pointer chain value) :
    StoredBytes s (pointer+16*chain.val) (bytes value) := by
  apply digest_bytes s _ value
  · omega
  · have := chain.isLt; omega
  · exact stored

theorem values_bytes (s : MachineState) (pointer : Nat) (values : Reference.Chain → Reference.Digest)
    (aligned : pointer%8=0) (bound : pointer+752 < 2^64)
    (stored : ∀ chain, CapturedValue s pointer chain (values chain)) :
    StoredBytes s pointer ((List.ofFn values).flatMap bytes) := by
  rw [KeygenLeaf.endpoints_eq]
  intro i hi
  have hi' : i < 46*16 := by simpa only [KeygenLeaf.endpointBytes,List.length_ofFn] using hi
  have chainBound : i/16 < 46 := by omega
  have valueBytes := captured_bytes s pointer ⟨i/16,chainBound⟩ (values ⟨i/16,chainBound⟩) aligned bound
    (stored ⟨i/16,chainBound⟩) (i%16) (by simp only [Memory.bytes_length]; omega)
  have address : pointer+16*(i/16)+i%16=pointer+i := by omega
  rw [address] at valueBytes
  simpa only [KeygenLeaf.endpointBytes,List.getElem_ofFn,bytes,List.getElem_map,List.getElem_range] using valueBytes

theorem upper_bytes (s : MachineState) (pointer : Nat) (signature : Reference.LayerSignature)
    (aligned : pointer%8=0) (bound : pointer+752 < 2^64)
    (stored : UpperLayerStored s pointer signature) : StoredBytes s pointer (layerBytes signature) := by
  apply StoredBytes.append
  · exact values_bytes s pointer signature.values aligned bound stored.1
  · have len : ((List.ofFn signature.values).flatMap bytes).length=736 := by simp [bytes]
    rw [len]
    exact digest_bytes s (pointer+736) signature.sibling (by omega) (by omega) stored.2

theorem bottom_bytes (s : MachineState) (pointer : Nat) (signature : Reference.LayerSignature)
    (aligned : pointer%8=0) (bound : pointer+32 < 2^64)
    (stored : BottomLayerStored s pointer signature) :
    StoredBytes s pointer (bytes (signature.values 0) ++ bytes signature.sibling) := by
  apply StoredBytes.append
  · apply digest_bytes s pointer (signature.values 0) aligned (by omega)
    simpa only [CapturedValue,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using stored.1
  · rw [Memory.bytes_length]
    exact digest_bytes s (pointer+16) signature.sibling (by omega) (by omega) stored.2

end SigGolfCandidate.Hypertree.SignWire
