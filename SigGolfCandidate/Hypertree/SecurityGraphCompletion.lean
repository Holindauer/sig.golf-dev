import SigGolfCandidate.Hypertree.SecurityGraphAuthorizationDisclosure

namespace SigGolfCandidate.Hypertree.SecurityGraphCompletion
open SigGolf Reference SecurityDerivation SecuritySeparation SecurityGraph SecurityGraphReference
  SecurityGraphIdeal SecurityRandomOracle
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A deterministic extension at one dummy secret key, used only to reuse deterministic
reference extraction. No distributional relationship with the sampled secret key is asserted. -/
noncomputable def residual (privateAnswers : PrivateTable) (base : Hash) : Hash :=
  fun query => if found : ∃ slot, input 0 slot = query then privateAnswers found.choose else base query

theorem residual_private (privateAnswers : PrivateTable) (base : Hash) (slot : Slot) :
    residual privateAnswers base (input 0 slot) = privateAnswers slot := by
  unfold residual
  split
  next found => rw [input_injective 0 found.choose_spec]
  next missing => exact False.elim (missing ⟨slot, rfl⟩)

theorem residual_public (privateAnswers : PrivateTable) (base : Hash) (query : Query)
    (safe : ¬SecretKeyEligible query) : residual privateAnswers base query = base query := by
  unfold residual
  split
  next found => obtain ⟨slot, same⟩ := found; exact False.elim (safe ⟨0, slot, same⟩)
  next missing => rfl

@[simp] theorem derived_residual (privateAnswers : PrivateTable) (base : Hash) :
    derived (residual privateAnswers base) 0 = privateAnswers := by
  funext slot
  exact residual_private privateAnswers base slot

noncomputable def hash (privateAnswers : PrivateTable) (graph : Labels) (base : Hash) : Hash :=
  programmed privateAnswers graph (residual privateAnswers base)

theorem hash_as_derived (privateAnswers : PrivateTable) (graph : Labels) (base : Hash) :
    hash privateAnswers graph base =
      programmed (derived (residual privateAnswers base) 0) graph (residual privateAnswers base) := by
  rw [derived_residual]
  rfl

theorem hash_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash) (query : Query)
    (safe : ¬SecretKeyEligible query) :
    hash privateAnswers graph base query = programmed privateAnswers graph base query := by
  unfold hash programmed
  split
  · rfl
  · exact residual_public privateAnswers base query safe

theorem query_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notChain : tag % 256 ≠ 1) (notNonce : tag % 256 ≠ 6) :
    query (hash privateAnswers graph base) tag level tree leaf chain step payload =
      query (programmed privateAnswers graph base) tag level tree leaf chain step payload :=
  hash_public privateAnswers graph base _
    (SecurityDomains.not_secretKeyEligible_addressedInput tag level tree leaf chain step payload notChain notNonce)

theorem chainHash_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level tree : Nat) (side : Bool) (chain : Chain) :
    chainHash (hash privateAnswers graph base) level tree side chain =
      chainHash (programmed privateAnswers graph base) level tree side chain := by
  funext step value
  unfold chainHash
  rw [query_public _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]

theorem compressLeaf_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    compressLeaf (hash privateAnswers graph base) level tree side values =
      compressLeaf (programmed privateAnswers graph base) level tree side values := by
  unfold compressLeaf
  rw [query_public _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]

theorem node_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level tree : Nat) (left right : Digest) :
    node (hash privateAnswers graph base) level tree left right =
      node (programmed privateAnswers graph base) level tree left right := by
  unfold node
  rw [query_public _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]

theorem index_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (pk : PublicKey) (message : Message) (nonce : Bytes 32) :
    indexOf (hash privateAnswers graph base) pk message nonce =
      indexOf (programmed privateAnswers graph base) pk message nonce := by
  unfold indexOf
  rw [query_public _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]

theorem recoverLeaf_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level tree : Nat) (side : Bool) (message : Digest) (signature : LayerSignature) :
    recoverLeaf (hash privateAnswers graph base) level tree side message signature =
      recoverLeaf (programmed privateAnswers graph base) level tree side message signature := by
  simp only [recoverLeaf, chainHash_public, compressLeaf_public]

theorem recoverLayer_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level tree : Nat) (side : Bool) (message : Digest) (signature : LayerSignature) :
    recoverLayer (hash privateAnswers graph base) level tree side message signature =
      recoverLayer (programmed privateAnswers graph base) level tree side message signature := by
  simp only [recoverLayer, recoverLeaf_public, node_public]

theorem recoverLayers_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level index : Nat) (message : Digest) (signatures : List LayerSignature) :
    recoverLayers (hash privateAnswers graph base) level index message signatures =
      recoverLayers (programmed privateAnswers graph base) level index message signatures := by
  induction signatures generalizing level index message with
  | nil => rfl
  | cons signature rest ih => simp only [recoverLayers, recoverLayer_public, ih]

/-- Actual arbitrary-witness verification is unchanged by the deterministic
completion, including attacker-chosen randomizers and malformed layer counts. -/
theorem verify_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (pk : PublicKey) (message : Message) (signature : Signature) :
    Reference.verify (hash privateAnswers graph base) pk message signature ↔
      Reference.verify (programmed privateAnswers graph base) pk message signature := by
  simp only [Reference.verify, index_public, recoverLayers_public]

theorem keygen_label (privateAnswers : PrivateTable) (graph : Labels) (base : Hash) :
    Reference.keygen (hash privateAnswers graph base) 0 = truncate (graph (.node 151 0)) := by
  rw [hash_as_derived]
  exact programmed_treeRoot (residual privateAnswers base) 0 graph 151 0

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphCompletion.verify_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms verify_public
end SigGolfCandidate.Hypertree.SecurityGraphCompletion
