import SigGolfCandidate.Hypertree.SecurityGraphCompletion

namespace SigGolfCandidate.Hypertree.SecurityGraphCompletion
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphReference
  SecurityGraphIdeal SecurityGraphSigner SecurityRandomOracle SignatureEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem secret_point (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (address : ChainAddress) :
    secret (hash privateAnswers graph base) 0 address.level.val address.tree.toNat
      address.side address.chain = chainPoint privateAnswers graph address 0 := by
  rw [hash_as_derived]
  simpa only [derived_residual, chainPoint, Fin.val_zero, ↓reduceDIte] using
    programmed_secret (residual privateAnswers base) 0 graph address

theorem treeRoot_label (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level : Fin 160) (tree : BitVec 192) :
    treeRoot (hash privateAnswers graph base) 0 level.val tree.toNat =
      truncate (graph (.node level tree)) := by
  rw [hash_as_derived]
  exact programmed_treeRoot (residual privateAnswers base) 0 graph level tree

theorem leafRoot_label (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    leafRoot (hash privateAnswers graph base) 0 level.val tree.toNat side =
      leafLabel graph level tree side := by
  rw [hash_as_derived]
  exact programmed_leafRoot (residual privateAnswers base) 0 graph level tree side

theorem upper_layer (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest)
    (positive : 0 < level.val) :
    signLayer (hash privateAnswers graph base) 0 level.val tree.toNat side message =
      layer privateAnswers graph level tree side message := by
  have values : (signLayer (hash privateAnswers graph base) 0 level.val tree.toNat side message).values =
      (layer privateAnswers graph level tree side message).values := by
    funext chain
    rw [hash_as_derived]
    have same := programmed_sign_fragment (residual privateAnswers base) 0 graph level tree side message chain
    simpa only [derived_residual, layer, show level.val ≠ 0 by omega, if_false] using same
  have sibling := leafRoot_label privateAnswers graph base level tree (!side)
  exact congrArg₂ LayerSignature.mk values sibling

theorem upper_layers (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (count level index : Nat) (levels : count + level ≤ 160) (bound : index < 2 ^ 192)
    (positive : 0 < level) (message : Digest) :
    signLayers (hash privateAnswers graph base) 0 count level index message =
      upperLayers privateAnswers graph count level index levels bound message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
    have leaf := upper_layer privateAnswers graph base ⟨level, by omega⟩
      (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message positive
    have root := treeRoot_label privateAnswers graph base ⟨level, by omega⟩
      (BitVec.ofNat 192 (index / 2))
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt half] at leaf root
    simp only [signLayers, upperLayers, leaf, root]
    exact congrArg (List.cons _) (ih (level + 1) (index / 2) (by omega) half (by omega) _)

theorem nonce_private (privateAnswers : PrivateTable) (graph : Labels) (base : Hash) (message : Message) :
    randomizer (hash privateAnswers graph base) 0 message = privateAnswers (.randomizer message) := by
  change programmed privateAnswers graph (residual privateAnswers base)
    (SecurityDerivation.input 0 (.randomizer message)) = _
  rw [programmed_private, residual_private]

/-- The deterministic completion reproduces the actual graph signature for every
private table; its dummy secret key is merely a proof device, never sampled or guessed. -/
theorem signCompact_graph (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (pk : PublicKey) (message : Message) :
    signCompact (hash privateAnswers graph base) 0 pk message =
      signature privateAnswers graph (privateAnswers (.randomizer message))
        (indexOf (programmed privateAnswers graph base) pk message (privateAnswers (.randomizer message))) := by
  let index := indexOf (programmed privateAnswers graph base) pk message (privateAnswers (.randomizer message))
  have bound : index.toNat / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..)
    (lt_of_lt_of_le index.isLt (Nat.pow_le_pow_right (by decide) (by decide)))
  have source := secret_point privateAnswers graph base
    ⟨0, BitVec.ofNat 192 (index.toNat / 2), index.toNat % 2 == 1, 0⟩
  have sibling := leafRoot_label privateAnswers graph base 0
    (BitVec.ofNat 192 (index.toNat / 2)) (!(index.toNat % 2 == 1))
  have root := treeRoot_label privateAnswers graph base 0 (BitVec.ofNat 192 (index.toNat / 2))
  simp only [Fin.val_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at source sibling root
  change (⟨randomizer (hash privateAnswers graph base) 0 message,
    secret (hash privateAnswers graph base) 0 0
      ((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat / 2)
      ((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat % 2 == 1) 0,
    leafRoot (hash privateAnswers graph base) 0 0
      ((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat / 2)
      (!((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat % 2 == 1)),
    signLayers (hash privateAnswers graph base) 0 159 1
      ((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat / 2)
      (treeRoot (hash privateAnswers graph base) 0 0
        ((indexOf (hash privateAnswers graph base) pk message (randomizer (hash privateAnswers graph base) 0 message)).toNat / 2))⟩ : Compact) = _
  simp only [nonce_private, index_public]
  change (⟨_, secret (hash privateAnswers graph base) 0 0 (index.toNat / 2) (index.toNat % 2 == 1) 0,
    leafRoot (hash privateAnswers graph base) 0 0 (index.toNat / 2) (!(index.toNat % 2 == 1)),
    signLayers (hash privateAnswers graph base) 0 159 1 (index.toNat / 2)
      (treeRoot (hash privateAnswers graph base) 0 0 (index.toNat / 2))⟩ : Compact) = _
  rw [source, sibling, root, upper_layers _ _ _ 159 1 _ (by decide) bound (by decide)]
  rfl

end SigGolfCandidate.Hypertree.SecurityGraphCompletion
