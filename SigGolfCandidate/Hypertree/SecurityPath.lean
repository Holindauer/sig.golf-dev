import SigGolfCandidate.Hypertree.SecurityExtraction

namespace SigGolfCandidate.Hypertree.SecurityPath
open SigGolf Reference SecurityExtraction
set_option maxRecDepth 4096

/-- The unique child-tree digest canonically authenticated at an upper address. -/
def canonicalChild (hash : Hash) (seed : Seed) (level index : Nat) : Digest :=
  treeRoot hash seed (level - 1) index

/-- A verifier exposes an earlier canonical chain point than the fragment for
this address's canonical child digest. This event still needs its ROM contact bound. -/
def EarlierPointExposure (hash : Hash) (seed : Seed) (level index : Nat)
    (message : Digest) (signature : LayerSignature) : Prop :=
  ∃ chain, (digit message chain).val < (digit (canonicalChild hash seed level index) chain).val ∧
    signature.values chain =
      walk (chainHash hash level (index / 2) (index % 2 == 1) chain) 0 (digit message chain).val
        (secret hash seed level (index / 2) (index % 2 == 1) chain)

def LayerFault (hash : Hash) (seed : Seed) (level index : Nat)
    (message : Digest) (signature : LayerSignature) : Prop :=
  LayerTargetCollision hash seed level (index / 2) (index % 2 == 1) message signature ∨
    (0 < level ∧ EarlierPointExposure hash seed level index message signature)

def PathFault (hash : Hash) (seed : Seed) : Nat → Nat → Digest → List LayerSignature → Prop
  | _, _, _, [] => False
  | level, index, message, signature :: rest =>
      LayerFault hash seed level index message signature ∨
        PathFault hash seed (level + 1) (index / 2)
          (recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest

def LayersAgree : Nat → List LayerSignature → List LayerSignature → Prop
  | _, [], [] => True
  | level, actual :: rest, expected :: rest' =>
      LayerAgrees level actual expected ∧ LayersAgree (level + 1) rest rest'
  | _, _, _ => False

/-- An accepted nonfaulty upper layer binds its input to the canonical child;
otherwise the checksum exposes an earlier canonical chain point. -/
theorem layer_binding_no_fault (hash : Hash) (seed : Seed) (level index : Nat)
    (message : Digest) (signature : LayerSignature)
    (accepted : recoverLayer hash level (index / 2) (index % 2 == 1) message signature =
      treeRoot hash seed level (index / 2))
    (clean : ¬LayerFault hash seed level index message signature) :
    (level = 0 ∨ message = canonicalChild hash seed level index) ∧
      LayerAgrees level signature (signLayer hash seed level (index / 2) (index % 2 == 1) message) := by
  classical
  rcases layer_canonical_or_collision hash seed level (index / 2) (index % 2 == 1)
    message signature accepted with agrees | collision
  · refine ⟨?_, agrees⟩
    by_cases bottom : level = 0
    · exact Or.inl bottom
    · right
      by_contra different
      have canonical (chain : Chain) : signature.values chain =
          walk (chainHash hash level (index / 2) (index % 2 == 1) chain) 0 (digit message chain).val
            (secret hash seed level (index / 2) (index % 2 == 1) chain) := by
        simpa only [signLayer, bottom, ↓reduceIte] using agrees.2 chain (Or.inl bottom)
      have exposure := changed_message_earlier_point hash seed level (index / 2) (index % 2 == 1)
        (canonicalChild hash seed level index) message signature (Ne.symm different) canonical
      exact clean (Or.inr ⟨by omega, exposure⟩)
  · exact False.elim (clean (Or.inl collision))

/-- The canonical terminal target is independent of every intermediate message.
Keeping this closed form avoids normalizing entire unused reference subtrees. -/
def terminalRoot (hash : Hash) (seed : Seed) (count level index : Nat) : Digest :=
  treeRoot hash seed (level + count - 1) (index / 2 ^ count)

theorem terminalRoot_succ (hash : Hash) (seed : Seed) (count level index : Nat) :
    terminalRoot hash seed (count + 1) level index =
      terminalRoot hash seed count (level + 1) (index / 2) := by
  unfold terminalRoot
  congr 1
  · omega
  · simp only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- Full hypertree extraction. A correctly recovered final root forces every
serialized layer to be canonical, unless an actual layer has a designated target
collision or exposes an earlier canonical point. No global injectivity is assumed. -/
theorem path_binding_no_fault (hash : Hash) (seed : Seed) (level index : Nat)
    (message : Digest) (signatures : List LayerSignature)
    (accepted : recoverLayers hash level index message signatures =
      terminalRoot hash seed signatures.length level index)
    (clean : ¬PathFault hash seed level index message signatures) :
    (level = 0 ∨ message = canonicalChild hash seed level index) ∧
      LayersAgree level signatures (signLayers hash seed signatures.length level index message) := by
  induction signatures generalizing level index message with
  | nil =>
    refine ⟨Or.inr ?_, trivial⟩
    simpa only [recoverLayers, List.length_nil, terminalRoot, Nat.add_zero, pow_zero,
      Nat.div_one, canonicalChild] using accepted
  | cons signature rest ih =>
    have cleanLayer : ¬LayerFault hash seed level index message signature := fun h => clean (Or.inl h)
    have cleanTail : ¬PathFault hash seed (level + 1) (index / 2)
        (recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest :=
      fun h => clean (Or.inr h)
    have tailAccepted : recoverLayers hash (level + 1) (index / 2)
        (recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest =
        terminalRoot hash seed rest.length (level + 1) (index / 2) := by
      rw [← terminalRoot_succ]
      exact accepted
    have tailBound := ih (level + 1) (index / 2) _ tailAccepted cleanTail
    have root : recoverLayer hash level (index / 2) (index % 2 == 1) message signature =
        treeRoot hash seed level (index / 2) := by
      rcases tailBound.1 with impossible | equal
      · omega
      · simpa only [canonicalChild, Nat.add_sub_cancel] using equal
    have layer := layer_binding_no_fault hash seed level index message signature root cleanLayer
    refine ⟨layer.1, layer.2, ?_⟩
    simpa only [root] using tailBound.2

theorem layerAgrees_eq_of_positive {level : Nat} (positive : 0 < level)
    {actual expected : LayerSignature} (agrees : LayerAgrees level actual expected) : actual = expected := by
  have values : actual.values = expected.values := funext fun chain => agrees.2 chain (Or.inl (by omega))
  have sibling := agrees.1
  cases actual
  cases expected
  cases values
  cases sibling
  rfl

theorem layersAgree_eq_of_positive {level : Nat} (positive : 0 < level)
    {actual expected : List LayerSignature} (agrees : LayersAgree level actual expected) : actual = expected := by
  induction actual generalizing level expected with
  | nil => cases expected <;> simp_all [LayersAgree]
  | cons head rest ih =>
    cases expected with
    | nil => exact False.elim agrees
    | cons head' rest' =>
      have first := layerAgrees_eq_of_positive positive agrees.1
      have tail := ih (by omega) agrees.2
      cases first
      cases tail
      rfl

/-- The canonical compact witness at an index and supplied randomizer. The nonce
is deliberately unconstrained here, matching the actual verifier. -/
def canonicalCompact (hash : Hash) (seed : Seed) (r : Bytes 32) (index : Nat) :
    SignatureEncoding.Compact :=
  ⟨r, secret hash seed 0 (index / 2) (index % 2 == 1) 0,
    leafRoot hash seed 0 (index / 2) (!(index % 2 == 1)),
    signLayers hash seed 159 1 (index / 2) (treeRoot hash seed 0 (index / 2))⟩

/-- Absence of path faults determines every compact signature byte, including all
upper WOTS fragments and siblings; no unused bottom fields enter the conclusion. -/
theorem compact_canonical_of_no_fault (hash : Hash) (seed : Seed) (message : Message)
    (signature : SignatureEncoding.Compact)
    (accepted : Reference.verify hash (Reference.keygen hash seed) message signature.toReference)
    (clean : ¬PathFault hash seed 0
      (indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat 0 signature.toReference.layers) :
    signature = canonicalCompact hash seed signature.randomizer
      (indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat := by
  have target : terminalRoot hash seed signature.toReference.layers.length 0
      (indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat = Reference.keygen hash seed := by
    rw [accepted.1]
    simp only [terminalRoot, Nat.zero_add, Nat.div_eq_of_lt
      (indexOf hash (Reference.keygen hash seed) message signature.randomizer).isLt]
    rfl
  have bound := (path_binding_no_fault hash seed 0
    (indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat 0 signature.toReference.layers
    (accepted.2.trans target.symm) clean).2
  rw [accepted.1] at bound
  change LayerAgrees 0
    ⟨fun i => if i = 0 then signature.bottom else 0, signature.sibling⟩
    (signLayer hash seed 0
      ((indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat / 2)
      ((indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat % 2 == 1) 0) ∧
    LayersAgree 1 signature.upper
      (signLayers hash seed 159 1
        ((indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat / 2)
        (treeRoot hash seed 0 ((indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat / 2))) at bound
  have bottom := bound.1.2 0 (Or.inr rfl)
  have sibling := bound.1.1
  have upper := layersAgree_eq_of_positive (by decide : 0 < 1) bound.2
  simp only [signLayer, ↓reduceIte] at bottom sibling
  cases signature
  dsimp only at bottom sibling upper ⊢
  unfold canonicalCompact
  congr

/-- A signature with the honest deterministic randomizer is unique outside the
extracted path-fault event. -/
theorem compact_unique_honest_randomizer (hash : Hash) (seed : Seed) (message : Message)
    (signature : SignatureEncoding.Compact)
    (accepted : Reference.verify hash (Reference.keygen hash seed) message signature.toReference)
    (randomizerEqual : signature.randomizer = randomizer hash seed message)
    (clean : ¬PathFault hash seed 0
      (indexOf hash (Reference.keygen hash seed) message signature.randomizer).toNat 0 signature.toReference.layers) :
    signature = SignatureEncoding.signCompact hash seed (Reference.keygen hash seed) message := by
  rw [compact_canonical_of_no_fault hash seed message signature accepted clean, randomizerEqual]
  rfl

end SigGolfCandidate.Hypertree.SecurityPath
