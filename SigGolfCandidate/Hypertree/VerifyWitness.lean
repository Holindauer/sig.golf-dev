import SigGolfCandidate.Hypertree.VerifyTreeExecution
import SigGolfCandidate.Hypertree.VerifyLoader
import SigGolfCandidate.Hypertree.SignAdvance

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- The original fixed-size witness is still present at the organizer's input address. -/
def WitnessStored (s : MachineState) (witness : Bytes signatureBytes) : Prop :=
  ∀ i, i < signatureBytes → s.getByte (BitVec.ofNat 64 (0x3d3b0+i)) = witness.extractLsb' (8*i) 8

theorem WitnessStored.loaded (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s) :
    WitnessStored s witness := loaded_witness pk message witness s loaded

theorem WitnessStored.transfer (s final : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness)
    (frame : ∀ a, a.toNat < 0x80000 → final.getMem a = s.getMem a) : WitnessStored final witness := by
  intro i hi
  rw [getByte_word final 0x3d3b0 i (by decide) (by change i < 119632 at hi; omega),
    frame _ (by change (0x3d3b0+8*(i/8)) % 2^64 < 0x80000; change i < 119632 at hi; omega),
    ← getByte_word s 0x3d3b0 i (by decide) (by change i < 119632 at hi; omega)]
  exact stored i hi

/-- An aligned machine load reads precisely the corresponding eight witness bytes. -/
theorem WitnessStored.word (s : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness) (offset : Nat)
    (aligned : offset % 8 = 0) (bound : offset+8 ≤ signatureBytes) :
    s.getMem (BitVec.ofNat 64 (0x3d3b0+offset)) = witness.extractLsb' (8*offset) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have quot : (offset+j)/8 = offset/8 := by omega
  have rem : (offset+j)%8 = j := by omega
  have mul : 8*(offset/8) = offset := by omega
  have bits : 64*(offset/8) = 8*offset := by omega
  have h := stored (offset+j) (by omega)
  rw [getByte_word s 0x3d3b0 (offset+j) (by decide) (by change offset+8 ≤ 119632 at bound; omega)] at h
  simp only [quot, rem, wordAddress, mul] at h
  rw [h]
  symm
  simpa only [quot, rem, bits] using KeygenNode.extractByte_slice witness (offset+j)

/-- Word-level interpretation of a serialized 128-bit field. -/
theorem WitnessStored.slice_word (s : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness) (start : Nat) (i : Fin 2)
    (aligned : start % 8 = 0) (bound : start+16 ≤ signatureBytes) :
    s.getMem (BitVec.ofNat 64 (0x3d3b0+start+8*i.val)) =
      (SignatureEncoding.slice witness start 16).extractLsb' (64*i.val) 64 := by
  have hi := i.isLt
  rw [Nat.add_assoc, stored.word s witness (start+8*i.val) (by omega) (by omega)]
  unfold SignatureEncoding.slice
  ext j hj
  have inside : 64*i.val+j < 128 := by omega
  have shift : 8*(start+8*i.val)+j = 8*start+(64*i.val+j) := by omega
  simp [inside, shift]

/-- Each layer's decoded values, omitting the unused bottom-chain entries. -/
def wireLayer (witness : Bytes signatureBytes) (level : Nat) : Reference.LayerSignature :=
  if level = 0 then ⟨fun chain => if chain = 0 then SignatureEncoding.slice witness 32 16 else 0,
    SignatureEncoding.slice witness 48 16⟩
  else SignatureEncoding.decodeLayer witness (level-1)

theorem wire_layer_value (s : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness) (level : Nat) (small : level < 160)
    (chain : Reference.Chain) (relevant : level ≠ 0 ∨ chain = 0) (i : Fin 2) :
    s.getMem (BitVec.ofNat 64 (0x3d3b0+layerOffset level+16*chain.val+8*i.val)) =
      ((wireLayer witness level).values chain).extractLsb' (64*i.val) 64 := by
  by_cases zero : level = 0
  · subst level
    have hc : chain = 0 := relevant.resolve_left (by simp)
    subst chain
    simpa [wireLayer, layerOffset] using stored.slice_word s witness 32 i (by decide) (by decide)
  · have hc := chain.isLt
    have bound : 64+752*(level-1)+16*chain.val+16 ≤ signatureBytes := by change _ ≤ 119632; omega
    have aligned : (64+752*(level-1)+16*chain.val) % 8 = 0 := by omega
    simpa [wireLayer, zero, layerOffset, SignatureEncoding.decodeLayer, Nat.add_assoc] using
      stored.slice_word s witness (64+752*(level-1)+16*chain.val) i aligned bound

theorem wire_layer_sibling (s : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness) (level : Nat) (small : level < 160) (i : Fin 2) :
    s.getMem (BitVec.ofNat 64 (0x3d3b0+layerOffset level+siblingOffset level+8*i.val)) =
      (wireLayer witness level).sibling.extractLsb' (64*i.val) 64 := by
  by_cases zero : level = 0
  · subst level
    simpa [wireLayer, layerOffset, siblingOffset] using stored.slice_word s witness 48 i (by decide) (by decide)
  · have bound : 64+752*(level-1)+736+16 ≤ signatureBytes := by change _ ≤ 119632; omega
    have aligned : (64+752*(level-1)+736) % 8 = 0 := by omega
    simpa [wireLayer, zero, layerOffset, siblingOffset, SignatureEncoding.decodeLayer, Nat.add_assoc] using
      stored.slice_word s witness (64+752*(level-1)+736) i aligned bound

/-- info: 'SigGolfCandidate.Hypertree.Verifying.wire_layer_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_layer_value

end SigGolfCandidate.Hypertree.Verifying
