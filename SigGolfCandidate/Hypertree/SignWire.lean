import SigGolfCandidate.Hypertree.SignWireBytes

namespace SigGolfCandidate.Hypertree.SignWire
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Signing SignatureEncoding
set_option maxRecDepth 4096

theorem upper_layers_bytes (s : MachineState) (level : Nat) (signatures : List Reference.LayerSignature)
    (positive : 0 < level) (bound : level+signatures.length ≤ 160)
    (stored : LayersStored s level signatures) :
    StoredBytes s (0x20060+layerOffset level) (signatures.flatMap layerBytes) := by
  induction signatures generalizing level with
  | nil => intro i hi; simp at hi
  | cons signature rest ih =>
    have lt : level < 160 := by simp only [List.length_cons] at bound; omega
    have valid := sign_pointer_valid level lt
    have first : UpperLayerStored s (0x20060+layerOffset level) signature := by
      have h := stored.1
      simpa only [LayerStored,if_neg (by omega : level ≠ 0)] using h
    have left := upper_bytes s (0x20060+layerOffset level) signature valid.2.2 (by have := valid.2.1; omega) first
    have right := ih (level+1) (by omega) (by simp only [List.length_cons] at bound; omega) stored.2
    rw [List.flatMap_cons]
    apply StoredBytes.append s _ _ _ left
    rw [layerBytes_length]
    have address : 0x20060+layerOffset level+752=0x20060+layerOffset (level+1) := by
      rw [layerOffset_succ,if_neg (by omega : level ≠ 0),Nat.add_assoc]
    rw [address]
    exact right

theorem read_wire (s : MachineState) (signature : Compact) (valid : signature.Valid)
    (stored : StoredBytes s 0x20060 signature.encode) :
    readBuffer s 0x20060 signatureBytes=signature.wire valid := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  have h := stored i (by rw [signature.valid_length valid]; exact hi)
  simpa only [← signature.wire_bytes valid,bytes,List.getElem_map,List.getElem_range] using h

/-- Captured layer words and the randomizer determine every byte of the canonical signature. -/
theorem read_reference (s : MachineState) (signature : Reference.Signature)
    (valid : signature.layers.length=160)
    (randomizer : ∀ i : Fin 4, s.getMem (wordAddress 0x20060 i.val) = signature.randomizer.extractLsb' (64*i.val) 64)
    (stored : LayersStored s 0 signature.layers) :
    readBuffer s 0x20060 signatureBytes =
      (Compact.ofReference signature valid).wire (Compact.ofReference_valid signature valid) := by
  rcases signature with ⟨r,layers⟩
  cases layers with
  | nil => simp at valid
  | cons bottom upper =>
    have upperLen : upper.length=159 := by change upper.length+1=160 at valid; omega
    let compact : Compact := ⟨r,bottom.values 0,bottom.sibling,upper⟩
    have compactValid : compact.Valid := upperLen
    have randomBytes : StoredBytes s 0x20060 (bytes r) :=
      words_bytes s 0x20060 r (by decide) (by decide) (fun i hi => randomizer ⟨i,hi⟩)
    have bottomStored : BottomLayerStored s 0x20080 bottom := stored.1
    have bottomBytes := bottom_bytes s 0x20080 bottom (by decide) (by decide) bottomStored
    have upperBytes := upper_layers_bytes s 1 upper (by decide) (by omega) stored.2
    have tail : StoredBytes s 0x20080 ((bytes (bottom.values 0) ++ bytes bottom.sibling) ++ upper.flatMap layerBytes) := by
      apply StoredBytes.append s _ _ _ bottomBytes
      simpa [List.length_append,Memory.bytes_length,layerOffset] using upperBytes
    have full := StoredBytes.append s 0x20060 (bytes r) _ randomBytes (by simpa only [Memory.bytes_length] using tail)
    have compactBytes : StoredBytes s 0x20060 compact.encode := by
      simpa only [compact,Compact.encode,List.append_assoc] using full
    have result := read_wire s compact compactValid compactBytes
    simpa only [compact,Compact.ofReference,List.getElem_cons_zero,List.drop_succ_cons,List.drop_zero] using result

/-- Actual signer output memory decodes to the canonical typed signature. -/
theorem read_sign (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (randomizer : ∀ i : Fin 4, s.getMem (wordAddress 0x20060 i.val) =
      (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64)
    (stored : LayersStored s 0 (Reference.sign hash secretKey pk message).layers) :
    readBuffer s 0x20060 signatureBytes =
      (signCompact hash secretKey pk message).wire (signCompact_valid hash secretKey pk message) := by
  exact read_reference s (Reference.sign hash secretKey pk message) (Reference.sign_layers_length _ _ _ _ _ _) randomizer stored

/-- info: 'SigGolfCandidate.Hypertree.SignWire.read_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_sign

end SigGolfCandidate.Hypertree.SignWire
