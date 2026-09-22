import SigGolfCandidate.Hypertree.SecurityGraphSigner

namespace SigGolfCandidate.Hypertree.SecurityGraphFrontier
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphReference SecurityGraphIdeal
  SecurityGraphSigner
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Point := ChainAddress × Fin 8

/-- Public graph metadata. Revealing all these coordinates is conservative: they
contain no upper-chain interior point and no private chain source. Bottom graph
outputs are public preimage targets, while their private sources remain hidden. -/
def MetadataAgree (first second : Labels) : Prop :=
  ∀ position, (match position with
    | .chain address step => address.level.val = 0 ∨ step.val = 6
    | _ => True) → first position = second position

theorem MetadataAgree.node {first second : Labels} (same : MetadataAgree first second)
    (level : Fin 160) (tree : BitVec 192) : first (.node level tree) = second (.node level tree) :=
  same _ trivial

theorem MetadataAgree.leaf {first second : Labels} (same : MetadataAgree first second)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    leafLabel first level tree side = leafLabel second level tree side := by
  unfold leafLabel
  split
  next bottom => rw [same _ (Or.inl bottom)]
  next upper => rw [same _ trivial]

/-- The precise chain points serialized by one layer. -/
def layerPoints (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) : Finset Point :=
  if level.val = 0 then {(⟨level, tree, side, 0⟩, 0)}
  else Finset.univ.image (fun chain : Chain => (⟨level, tree, side, chain⟩, digit message chain))

/-- Modifying every unrevealed source/interior point leaves the actual layer fields
unchanged. The only required point equalities are those explicitly serialized. -/
theorem layer_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (level : Fin 160) (tree : BitVec 192)
    (side : Bool) (message : Digest)
    (revealed : ∀ point ∈ layerPoints level tree side message,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    layer privateFirst first level tree side message = layer privateSecond second level tree side message := by
  unfold layer
  congr 1
  · by_cases bottom : level.val = 0
    · simp only [if_pos bottom]
      funext chain
      split
      next zero =>
        exact revealed (⟨level, tree, side, 0⟩, 0) (by simp [layerPoints, bottom])
      next notZero => rfl
    · simp only [if_neg bottom]
      funext chain
      exact revealed (⟨level, tree, side, chain⟩, digit message chain)
        (by simp [layerPoints, bottom])
  · exact metadata.leaf level tree (!side)

/-- All upper-layer point reveals along the actual signature path. The selection
of each next layer's points depends only on public node metadata. -/
def upperPoints (labels : Labels) :
    (count level index : Nat) → count + level ≤ 160 → index < 2 ^ 192 → Digest → Finset Point
  | 0, _, _, _, _, _ => ∅
  | count + 1, level, index, hl, hi, message =>
      let atLevel : Fin 160 := ⟨level, by omega⟩
      let tree := BitVec.ofNat 192 (index / 2)
      layerPoints atLevel tree (index % 2 == 1) message ∪
        upperPoints labels count (level + 1) (index / 2) (by omega)
          (lt_of_le_of_lt (Nat.div_le_self ..) hi) (truncate (labels (.node atLevel tree)))

/-- Entire upper signing is insensitive to changes outside its revealed points. -/
theorem upper_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (count level index : Nat)
    (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest)
    (revealed : ∀ point ∈ upperPoints first count level index hl hi message,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    upperLayers privateFirst first count level index hl hi message =
      upperLayers privateSecond second count level index hl hi message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [upperLayers]
    apply congrArg₂ List.cons
    · apply layer_congr privateFirst privateSecond first second metadata
      intro point member
      exact revealed point (Finset.mem_union_left _ member)
    · rw [← metadata.node]
      apply ih
      intro point member
      exact revealed point (Finset.mem_union_right _ member)

/-- The reveal set itself is determined by public metadata and the message index,
so choosing which coordinates signing opens does not inspect their hidden values. -/
theorem upperPoints_congr (first second : Labels) (metadata : MetadataAgree first second)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    upperPoints first count level index hl hi message = upperPoints second count level index hl hi message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [upperPoints]
    rw [← metadata.node]
    rw [ih]

private theorem index_bound (index : BitVec 160) : index.toNat / 2 < 2 ^ 192 := by
  have bound : (2 : Nat) ^ 160 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
  exact lt_of_le_of_lt (Nat.div_le_self ..) (lt_of_lt_of_le index.isLt bound)

/-- Complete finite point disclosure made by one signature. -/
def signaturePoints (labels : Labels) (index : BitVec 160) : Finset Point :=
  let tree := BitVec.ofNat 192 (index.toNat / 2)
  let side := index.toNat % 2 == 1
  layerPoints 0 tree side 0 ∪
    upperPoints labels 159 1 (index.toNat / 2) (by decide) (index_bound index)
      (truncate (labels (.node 0 tree)))

theorem signaturePoints_congr (first second : Labels) (metadata : MetadataAgree first second)
    (index : BitVec 160) : signaturePoints first index = signaturePoints second index := by
  unfold signaturePoints
  dsimp only
  rw [← metadata.node]
  rw [upperPoints_congr first second metadata]

private theorem compact_congr (r : Bytes 32) {bottom bottom' sibling sibling' : Digest}
    {upper upper' : List LayerSignature} (hb : bottom = bottom') (hs : sibling = sibling')
    (hu : upper = upper') :
    (⟨r, bottom, sibling, upper⟩ : SignatureEncoding.Compact) = ⟨r, bottom', sibling', upper'⟩ := by
  cases hb; cases hs; cases hu; rfl

/-- Complete compact-signature noninterference: unopened chain coordinates can be
changed arbitrarily, while all serialized bytes remain the same. -/
theorem signature_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (r : Bytes 32) (index : BitVec 160)
    (revealed : ∀ point ∈ signaturePoints first index,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    signature privateFirst first r index = signature privateSecond second r index := by
  unfold signature
  dsimp only
  apply compact_congr
  · apply revealed (⟨0, BitVec.ofNat 192 (index.toNat / 2), index.toNat % 2 == 1, 0⟩, 0)
    apply Finset.mem_union_left
    simp [layerPoints]
  · exact metadata.leaf _ _ _
  · rw [← metadata.node]
    apply upper_congr privateFirst privateSecond first second metadata
    intro point member
    exact revealed point (Finset.mem_union_right _ member)

/-- Noninterference stated directly for the actual monadic signer, including its
secret deterministic randomizer and its actual residual-oracle message index. -/
theorem signer_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (residual : Hash) (pk : PublicKey) (message : Message)
    (nonce : privateFirst (.randomizer message) = privateSecond (.randomizer message))
    (revealed : ∀ point ∈ signaturePoints first
        ((residual (SecurityRandomOracle.indexInput pk message (privateFirst (.randomizer message)))).extractLsb' 0 160),
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    evalWithAnswerFn (answers privateFirst (programmed privateFirst first residual))
      (SecurityIdealSign.signCompact pk message) =
    evalWithAnswerFn (answers privateSecond (programmed privateSecond second residual))
      (SecurityIdealSign.signCompact pk message) := by
  rw [eval_signCompact, eval_signCompact, ← nonce]
  exact signature_congr privateFirst privateSecond first second metadata _ _ revealed


end SigGolfCandidate.Hypertree.SecurityGraphFrontier
