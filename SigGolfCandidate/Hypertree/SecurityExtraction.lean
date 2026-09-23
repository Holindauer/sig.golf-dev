import SigGolfCandidate.Hypertree.SecurityVerify
import SigGolfCandidate.Hypertree.Encoding

namespace SigGolfCandidate.Hypertree.SecurityExtraction
open SigGolf Reference SecurityRandomOracle SecurityPacking SignatureEncoding

/-- At one fixed address, the exact public H input determines its entire payload. -/
theorem addressedInput_payload_injective (tag level tree leaf chain step : Nat) :
    Function.Injective (addressedInput tag level tree leaf chain step) := by
  intro first second same
  exact List.append_cancel_left (packed_injective same)

/-- A real 128-bit target collision at one serialized address, not global hash injectivity. -/
def CollisionAt (hash : Hash) (tag level tree leaf chain step : Nat)
    (expected actual : List Byte) : Prop :=
  addressedInput tag level tree leaf chain step actual ≠
      addressedInput tag level tree leaf chain step expected ∧
    truncate (query hash tag level tree leaf chain step actual) =
      truncate (query hash tag level tree leaf chain step expected)

theorem collisionAt_of_payload_ne (hash : Hash) (tag level tree leaf chain step : Nat)
    (expected actual : List Byte) (different : actual ≠ expected)
    (same : truncate (query hash tag level tree leaf chain step actual) =
      truncate (query hash tag level tree leaf chain step expected)) :
    CollisionAt hash tag level tree leaf chain step expected actual :=
  ⟨fun h => different (addressedInput_payload_injective tag level tree leaf chain step h), same⟩

/-- Two unequal walks ending at one value must merge at a concrete step. -/
theorem walk_merge {α : Type} (f : Nat → α → α) (start steps : Nat) (expected actual : α)
    (different : actual ≠ expected) (same : walk f start steps actual = walk f start steps expected) :
    ∃ offset, offset < steps ∧
      walk f start offset actual ≠ walk f start offset expected ∧
      f (start + offset) (walk f start offset actual) =
        f (start + offset) (walk f start offset expected) := by
  classical
  induction steps generalizing start expected actual with
  | zero => exact False.elim (different same)
  | succ steps ih =>
    rcases Classical.em (f start actual = f start expected) with merge | merge
    · exact ⟨0, by omega, different, by simpa [walk] using merge⟩
    · obtain ⟨offset, bound, ne, eq⟩ := ih (start + 1) (f start expected) (f start actual) merge same
      refine ⟨offset + 1, by omega, ?_, ?_⟩
      · simpa only [walk] using ne
      · simpa only [walk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using eq

/-- A changed fragment that still reaches its correct WOTS endpoint exposes an
actual tag-2 target collision along the verifier's chain suffix. -/
theorem changed_fragment_collision (hash : Hash) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (message : Digest) (chain : Chain) (fragment : Digest)
    (different : fragment ≠ walk (chainHash hash level tree side chain) 0 (digit message chain).val
      (secret hash secretKey level tree side chain))
    (same : walk (chainHash hash level tree side chain) (digit message chain).val
      (7 - (digit message chain).val) fragment = endpoint hash secretKey level tree side chain) :
    ∃ offset, offset < 7 - (digit message chain).val ∧
      CollisionAt hash 2 level tree (sideNumber side) chain.val ((digit message chain).val + offset)
        (bytes (walk (chainHash hash level tree side chain) 0 ((digit message chain).val + offset)
          (secret hash secretKey level tree side chain)))
        (bytes (walk (chainHash hash level tree side chain) (digit message chain).val offset fragment)) := by
  have canonical := recover_chain (chainHash hash level tree side chain)
    (secret hash secretKey level tree side chain) (digit message chain)
  obtain ⟨offset, bound, ne, eq⟩ := walk_merge (chainHash hash level tree side chain)
    (digit message chain).val (7 - (digit message chain).val)
    (walk (chainHash hash level tree side chain) 0 (digit message chain).val
      (secret hash secretKey level tree side chain)) fragment different (same.trans canonical.symm)
  refine ⟨offset, bound, ?_⟩
  have splitWalk := walk_append (chainHash hash level tree side chain) 0 (digit message chain).val offset
    (secret hash secretKey level tree side chain)
  simp only [Nat.zero_add] at splitWalk
  rw [splitWalk]
  exact collisionAt_of_payload_ne hash 2 level tree (sideNumber side) chain.val _ _ _
    (fun h => ne (bytes_injective 16 h)) eq

/-- A leaf-compression collision is the only alternative to all recovered WOTS
endpoints equalling their designated canonical endpoints. -/
theorem upper_leaf_binding (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (upper : level ≠ 0)
    (same : recoverLeaf hash level tree side message signature = leafRoot hash secretKey level tree side) :
    (∀ chain, walk (chainHash hash level tree side chain) (digit message chain).val
      (7 - (digit message chain).val) (signature.values chain) = endpoint hash secretKey level tree side chain) ∨
    CollisionAt hash 3 level tree (sideNumber side) 0 0
      ((List.ofFn (endpoint hash secretKey level tree side)).flatMap bytes)
      ((List.ofFn (fun chain => walk (chainHash hash level tree side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain))).flatMap bytes) := by
  classical
  simp only [recoverLeaf, leafRoot, upper, ↓reduceIte, compressLeaf] at same
  by_cases equalPayload :
      ((List.ofFn (fun chain => walk (chainHash hash level tree side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain))).flatMap bytes) =
      ((List.ofFn (endpoint hash secretKey level tree side)).flatMap bytes)
  · left
    have values := flatMap_injective (bytes (n := 16)) 16 (by decide) (fun _ => by simp)
      (bytes_injective 16) equalPayload
    exact congrFun (List.ofFn_injective values)
  · exact Or.inr (collisionAt_of_payload_ne hash 3 level tree (sideNumber side) 0 0 _ _ equalPayload same)

/-- Root equality binds both ordered children unless the actual tag-4 node query
hits the canonical node target with a different input. -/
theorem node_binding (hash : Hash) (level tree : Nat)
    (left right actualLeft actualRight : Digest)
    (same : node hash level tree actualLeft actualRight = node hash level tree left right) :
    (actualLeft = left ∧ actualRight = right) ∨
      CollisionAt hash 4 level tree 0 0 0 (bytes left ++ bytes right)
        (bytes actualLeft ++ bytes actualRight) := by
  classical
  by_cases payload : bytes actualLeft ++ bytes actualRight = bytes left ++ bytes right
  · exact Or.inl ⟨bytes_injective 16 (List.append_inj_left payload (by simp)),
      bytes_injective 16 (List.append_inj_right payload (by simp))⟩
  · exact Or.inr (collisionAt_of_payload_ne hash 4 level tree 0 0 0 _ _ payload same)

/-- Each accepted layer either binds its selected leaf and sibling, or identifies
a concrete collision against that layer's designated canonical root. -/
theorem layer_binding (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature)
    (same : recoverLayer hash level tree side message signature = treeRoot hash secretKey level tree) :
    (recoverLeaf hash level tree side message signature = leafRoot hash secretKey level tree side ∧
      signature.sibling = leafRoot hash secretKey level tree (!side)) ∨
    CollisionAt hash 4 level tree 0 0 0
      (bytes (leafRoot hash secretKey level tree false) ++ bytes (leafRoot hash secretKey level tree true))
      (if side then bytes signature.sibling ++ bytes (recoverLeaf hash level tree side message signature)
        else bytes (recoverLeaf hash level tree side message signature) ++ bytes signature.sibling) := by
  cases side with
  | false => exact node_binding hash level tree _ _ _ _ same
  | true =>
    rcases node_binding hash level tree _ _ _ _ same with children | collision
    · exact Or.inl children.symm
    · exact Or.inr collision

/-- The bottom layer authenticates its one serialized preimage directly. -/
theorem bottom_leaf_binding (hash : Hash) (secretKey : SecretKey) (tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature)
    (same : recoverLeaf hash 0 tree side message signature = leafRoot hash secretKey 0 tree side) :
    signature.values 0 = secret hash secretKey 0 tree side 0 ∨
      CollisionAt hash 2 0 tree (sideNumber side) 0 0
        (bytes (secret hash secretKey 0 tree side 0)) (bytes (signature.values 0)) := by
  classical
  by_cases equal : signature.values 0 = secret hash secretKey 0 tree side 0
  · exact Or.inl equal
  · refine Or.inr (collisionAt_of_payload_ne hash 2 0 tree (sideNumber side) 0 0 _ _
      (fun h => equal (bytes_injective 16 h)) ?_)
    simpa only [recoverLeaf, leafRoot, ↓reduceIte, chainHash, Fin.val_zero] using same

/-- When a changed message has only canonical recovered fragments, the checksum
forces disclosure of a canonical chain point earlier than the signed fragment.
The random-oracle proof must charge this hidden-point exposure explicitly. -/
theorem changed_message_earlier_point (hash : Hash) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (signedMessage forgedMessage : Digest) (signature : LayerSignature)
    (different : signedMessage ≠ forgedMessage)
    (canonical : ∀ chain, signature.values chain =
      walk (chainHash hash level tree side chain) 0 (digit forgedMessage chain).val
        (secret hash secretKey level tree side chain)) :
    ∃ chain, (digit forgedMessage chain).val < (digit signedMessage chain).val ∧
      signature.values chain =
        walk (chainHash hash level tree side chain) 0 (digit forgedMessage chain).val
          (secret hash secretKey level tree side chain) := by
  obtain ⟨chain, earlier⟩ := distinct_digest_has_earlier_digit signedMessage forgedMessage different
  exact ⟨chain, earlier, canonical chain⟩

/-- Collisions against designated reference targets actually evaluated by one
verifier layer. This retains the canonical target, address, and forged payload. -/
def LayerTargetCollision (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) : Prop :=
  CollisionAt hash 4 level tree 0 0 0
    (bytes (leafRoot hash secretKey level tree false) ++ bytes (leafRoot hash secretKey level tree true))
    (if side then bytes signature.sibling ++ bytes (recoverLeaf hash level tree side message signature)
      else bytes (recoverLeaf hash level tree side message signature) ++ bytes signature.sibling) ∨
  (if level = 0 then
    CollisionAt hash 2 0 tree (sideNumber side) 0 0
      (bytes (secret hash secretKey 0 tree side 0)) (bytes (signature.values 0))
  else
    CollisionAt hash 3 level tree (sideNumber side) 0 0
      ((List.ofFn (endpoint hash secretKey level tree side)).flatMap bytes)
      ((List.ofFn (fun chain => walk (chainHash hash level tree side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain))).flatMap bytes) ∨
    ∃ chain offset, offset < 7 - (digit message chain).val ∧
      CollisionAt hash 2 level tree (sideNumber side) chain.val ((digit message chain).val + offset)
        (bytes (walk (chainHash hash level tree side chain) 0 ((digit message chain).val + offset)
          (secret hash secretKey level tree side chain)))
        (bytes (walk (chainHash hash level tree side chain) (digit message chain).val offset
          (signature.values chain))))

/-- Equality of precisely the layer data serialized on the wire. -/
def LayerAgrees (level : Nat) (actual expected : LayerSignature) : Prop :=
  actual.sibling = expected.sibling ∧
    ∀ chain, level ≠ 0 ∨ chain = 0 → actual.values chain = expected.values chain

/-- An accepted layer equals the canonical signature for its recovered child
unless one of its own public queries hits a designated target with a different input.
This theorem alone does not bound hidden canonical-point exposure on new messages. -/
theorem layer_canonical_or_collision (hash : Hash) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (message : Digest) (signature : LayerSignature)
    (same : recoverLayer hash level tree side message signature = treeRoot hash secretKey level tree) :
    LayerAgrees level signature (signLayer hash secretKey level tree side message) ∨
      LayerTargetCollision hash secretKey level tree side message signature := by
  classical
  rcases layer_binding hash secretKey level tree side message signature same with ⟨leaf, sibling⟩ | collision
  · by_cases bottom : level = 0
    · subst level
      rcases bottom_leaf_binding hash secretKey tree side message signature leaf with equal | collision
      · left
        refine ⟨sibling, ?_⟩
        intro chain only
        have hc : chain = 0 := by simpa using only
        subst chain
        simpa only [signLayer, ↓reduceIte] using equal
      · right
        exact Or.inr (by simpa only [↓reduceIte] using collision)
    · rcases upper_leaf_binding hash secretKey level tree side message signature bottom leaf with endpoints | collision
      · by_cases allCanonical : ∀ chain, signature.values chain =
          walk (chainHash hash level tree side chain) 0 (digit message chain).val
            (secret hash secretKey level tree side chain)
        · left
          exact ⟨sibling, fun chain _ => by simpa only [signLayer, bottom, ↓reduceIte] using allCanonical chain⟩
        · push Not at allCanonical
          obtain ⟨chain, different⟩ := allCanonical
          obtain ⟨offset, bound, collision⟩ := changed_fragment_collision hash secretKey level tree side
            message chain (signature.values chain) different (endpoints chain)
          right
          exact Or.inr (by simp only [bottom, ↓reduceIte]; exact Or.inr ⟨chain, offset, bound, collision⟩)
      · right
        exact Or.inr (by simp only [bottom, ↓reduceIte]; exact Or.inl collision)
  · exact Or.inr (Or.inl collision)

end SigGolfCandidate.Hypertree.SecurityExtraction
