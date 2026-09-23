import SigGolfCandidate.Hypertree.SecurityPacking
import SigGolfCandidate.Serialization

namespace SigGolfCandidate.Hypertree.SignatureEncoding
open SigGolf Reference

/-- The wire format has one bottom preimage and sibling, followed by full upper-layer signatures. -/
structure Compact where
  randomizer : Bytes 32
  bottom : Digest
  sibling : Digest
  upper : List LayerSignature

def Compact.Valid (signature : Compact) : Prop := signature.upper.length = 159

def Compact.toReference (signature : Compact) : Signature :=
  ⟨signature.randomizer, ⟨fun i => if i = 0 then signature.bottom else 0, signature.sibling⟩ :: signature.upper⟩

def layerBytes (signature : LayerSignature) : List Byte :=
  (List.ofFn signature.values).flatMap bytes ++ bytes signature.sibling

def Compact.encode (signature : Compact) : List Byte :=
  bytes signature.randomizer ++ bytes signature.bottom ++ bytes signature.sibling ++ signature.upper.flatMap layerBytes

/-- Fixed-width encodings have unambiguous concatenation. -/
theorem flatMap_injective {α β : Type} (encode : α → List β) (width : Nat)
    (positive : 0 < width) (length : ∀ x, (encode x).length = width)
    (injective : Function.Injective encode) : Function.Injective (List.flatMap encode) := by
  intro first second heq
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons y ys =>
      have sizes := congrArg List.length heq
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append, length] at sizes
      omega
  | cons x xs ih =>
    cases second with
    | nil =>
      have sizes := congrArg List.length heq
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append, length] at sizes
      omega
    | cons y ys =>
      simp only [List.flatMap_cons] at heq
      have head := injective (List.append_inj_left heq (by rw [length, length]))
      have tail := ih (List.append_inj_right heq (by rw [length, length]))
      cases head
      cases tail
      rfl

theorem layerBytes_length (signature : LayerSignature) : (layerBytes signature).length = 752 := by
  simp [layerBytes, bytes]

theorem layerBytes_injective : Function.Injective layerBytes := by
  intro first second heq
  have prefixLength : ((List.ofFn first.values).flatMap bytes).length = ((List.ofFn second.values).flatMap bytes).length := by
    simp [bytes]
  have values := flatMap_injective (bytes (n := 16)) 16 (by decide) (fun _ => by simp)
    (SecurityPacking.bytes_injective 16) (List.append_inj_left heq prefixLength)
  have valuesEq := List.ofFn_injective values
  have siblingEq := SecurityPacking.bytes_injective 16 (List.append_inj_right heq prefixLength)
  cases first
  cases second
  cases valuesEq
  cases siblingEq
  rfl

theorem Compact.encode_length (signature : Compact) :
    signature.encode.length = 64 + 752 * signature.upper.length := by
  simp only [Compact.encode, List.length_append, Memory.bytes_length, List.length_flatMap]
  have sum : (signature.upper.map (fun x => (layerBytes x).length)).sum = 752 * signature.upper.length := by
    simp [layerBytes_length, List.sum_replicate, Nat.mul_comm]
  omega

theorem Compact.valid_length (signature : Compact) (valid : signature.Valid) :
    signature.encode.length = signatureBytes := by
  rw [signature.encode_length, valid]
  rfl

theorem Compact.encode_injective : Function.Injective Compact.encode := by
  intro first second heq
  simp only [Compact.encode, List.append_assoc] at heq
  have randomizerEq := SecurityPacking.bytes_injective 32 (List.append_inj_left heq (by simp))
  have rest := List.append_inj_right heq (by simp)
  have bottomEq := SecurityPacking.bytes_injective 16 (List.append_inj_left rest (by simp))
  have rest' := List.append_inj_right rest (by simp)
  have siblingEq := SecurityPacking.bytes_injective 16 (List.append_inj_left rest' (by simp))
  have upperEq := flatMap_injective layerBytes 752 (by decide) layerBytes_length layerBytes_injective
    (List.append_inj_right rest' (by simp))
  cases first
  cases second
  cases randomizerEq
  cases bottomEq
  cases siblingEq
  cases upperEq
  rfl

/-- Only the first bottom-layer value is consumed; the other entries are absent from the wire format. -/
theorem recover_bottom (hash : Hash) (tree : Nat) (side : Bool) (message : Digest) (signature : LayerSignature) :
    recoverLayer hash 0 tree side message ⟨fun i => if i = 0 then signature.values 0 else 0, signature.sibling⟩ =
      recoverLayer hash 0 tree side message signature := by
  simp [recoverLayer, recoverLeaf]

/-- The submitted fixed-width object, with no padding or unused encoded fields. -/
def Compact.wire (signature : Compact) (valid : signature.Valid) : Bytes signatureBytes :=
  (Reference.packed signature.encode).2.cast (by
    change 8 * signature.encode.length = 8 * signatureBytes
    rw [signature.valid_length valid])

theorem Compact.wire_injective (first second : Compact) (hfirst : first.Valid) (hsecond : second.Valid)
    (same : first.wire hfirst = second.wire hsecond) : first = second := by
  apply Compact.encode_injective
  apply SecurityPacking.packed_injective
  apply Serialization.query_eq
  · change 8 * first.encode.length = 8 * second.encode.length
    rw [first.valid_length hfirst, second.valid_length hsecond]
  · have hv := congrArg BitVec.toNat same
    simpa only [Compact.wire, BitVec.toNat_cast] using hv

theorem Compact.wire_bytes (signature : Compact) (valid : signature.Valid) :
    bytes (signature.wire valid) = signature.encode := by
  apply SecurityPacking.packed_injective
  rw [Serialization.packed_bytes]
  apply Serialization.query_eq
  · change 8 * signatureBytes = 8 * signature.encode.length
    rw [signature.valid_length valid]
  · simp only [Compact.wire, BitVec.toNat_cast]

/-- Drop the bottom-layer fields that are never serialized or read by verification. -/
def Compact.ofReference (signature : Signature) (valid : signature.layers.length = 160) : Compact where
  randomizer := signature.randomizer
  bottom := (signature.layers[0]'(by omega)).values 0
  sibling := (signature.layers[0]'(by omega)).sibling
  upper := signature.layers.drop 1

theorem Compact.ofReference_valid (signature : Signature) (valid : signature.layers.length = 160) :
    (Compact.ofReference signature valid).Valid := by
  simp [Compact.Valid, Compact.ofReference, valid]

/-- Removing the unencoded bottom fields leaves verification unchanged. -/
theorem Compact.ofReference_verify (hash : Hash) (pk : PublicKey) (message : Message)
    (signature : Signature) (valid : signature.layers.length = 160) :
    Reference.verify hash pk message (Compact.ofReference signature valid).toReference ↔
      Reference.verify hash pk message signature := by
  rcases signature with ⟨randomizer, layers⟩
  cases layers with
  | nil => simp at valid
  | cons bottom upper =>
    simp only [Compact.ofReference, Compact.toReference, List.getElem_cons_zero,
      List.drop_succ_cons, List.drop_zero, Reference.verify, recoverLayers, recover_bottom, List.length_cons]

def signCompact (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) : Compact :=
  Compact.ofReference (Reference.sign hash secretKey pk message) (sign_layers_length _ _ _ _ _ _)

theorem signCompact_valid (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    (signCompact hash secretKey pk message).Valid := Compact.ofReference_valid _ _

/-- The canonical wire-format signature retains the reference scheme's all-oracle correctness. -/
theorem signCompact_correct (hash : Hash) (secretKey : SecretKey) (message : Message) :
    Reference.verify hash (Reference.keygen hash secretKey) message (signCompact hash secretKey (Reference.keygen hash secretKey) message).toReference := by
  apply (Compact.ofReference_verify _ _ _ _ _).mpr
  exact Reference.correct hash secretKey message

/-- info: 'SigGolfCandidate.Hypertree.SignatureEncoding.Compact.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Compact.encode_injective

/-- info: 'SigGolfCandidate.Hypertree.SignatureEncoding.signCompact_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signCompact_correct

end SigGolfCandidate.Hypertree.SignatureEncoding
