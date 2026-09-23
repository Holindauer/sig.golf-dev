import SigGolfCandidate.Hypertree.SecurityGraphCompletionSign

namespace SigGolfCandidate.Hypertree.SecurityGraphCollision
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphReference SecurityGraphIdeal
  SecurityGraphCompletion SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A layer's concrete collision alternatives, stated solely using public graph
labels, private source coordinates, and the actual public verification hash. -/
def LayerCollision (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool)
    (message : Digest) (signature : LayerSignature) : Prop :=
  let publicHash := programmed privateAnswers graph base
  CollisionAt publicHash 4 level.val tree.toNat 0 0 0
    (bytes (leafLabel graph level tree false) ++ bytes (leafLabel graph level tree true))
    (if side then bytes signature.sibling ++ bytes (recoverLeaf publicHash level.val tree.toNat side message signature)
      else bytes (recoverLeaf publicHash level.val tree.toNat side message signature) ++ bytes signature.sibling) ∨
  (if level.val = 0 then
    CollisionAt publicHash 2 0 tree.toNat (sideNumber side) 0 0
      (bytes (chainPoint privateAnswers graph ⟨level, tree, side, 0⟩ 0)) (bytes (signature.values 0))
  else
    CollisionAt publicHash 3 level.val tree.toNat (sideNumber side) 0 0
      ((List.ofFn fun chain => truncate (graph (.chain ⟨level, tree, side, chain⟩ 6))).flatMap bytes)
      ((List.ofFn (fun chain => walk (chainHash publicHash level.val tree.toNat side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain))).flatMap bytes) ∨
    ∃ chain offset, ∃ within : offset < 7 - (digit message chain).val,
      CollisionAt publicHash 2 level.val tree.toNat (sideNumber side) chain.val ((digit message chain).val + offset)
        (bytes (chainPoint privateAnswers graph ⟨level, tree, side, chain⟩
          ⟨(digit message chain).val + offset, by have := (digit message chain).isLt; omega⟩))
        (bytes (walk (chainHash publicHash level.val tree.toNat side chain) (digit message chain).val offset
          (signature.values chain))))

theorem collision_public (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (tag level tree leaf chain step : Nat) (expected actual : List Byte)
    (notChain : tag % 256 ≠ 1) (notNonce : tag % 256 ≠ 6) :
    CollisionAt (hash privateAnswers graph base) tag level tree leaf chain step expected actual ↔
      CollisionAt (programmed privateAnswers graph base) tag level tree leaf chain step expected actual := by
  simp only [CollisionAt, query_public _ _ _ _ _ _ _ _ _ _ notChain notNonce]

theorem completed_walk (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (address : ChainAddress) (point : Fin 8) :
    walk (chainHash (hash privateAnswers graph base) address.level.val address.tree.toNat address.side address.chain)
      0 point.val (secret (hash privateAnswers graph base) 0 address.level.val address.tree.toNat address.side address.chain) =
      chainPoint privateAnswers graph address point := by
  rw [hash_as_derived]
  simpa only [derived_residual] using programmed_walk (residual privateAnswers base) 0 graph address point.val
    (by have := point.isLt; omega)

theorem completed_endpoint (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (address : ChainAddress) :
    endpoint (hash privateAnswers graph base) 0 address.level.val address.tree.toNat address.side address.chain =
      truncate (graph (.chain address 6)) := by
  rw [hash_as_derived]
  exact programmed_endpoint (residual privateAnswers base) 0 graph address

/-- Deterministic reference extraction transports to the arbitrary-private graph
without leaving any secret key-realizability premise in the collision statement. -/
theorem layer_collision (privateAnswers : PrivateTable) (graph : Labels) (base : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) (signature : LayerSignature)
    (collision : LayerTargetCollision (hash privateAnswers graph base) 0 level.val tree.toNat side message signature) :
    LayerCollision privateAnswers graph base level tree side message signature := by
  unfold LayerTargetCollision at collision
  unfold LayerCollision
  dsimp only
  rcases collision with nodeHit | other
  · left
    rw [leafRoot_label, leafRoot_label, recoverLeaf_public] at nodeHit
    exact (collision_public _ _ _ 4 _ _ _ _ _ _ _ (by decide) (by decide)).mp nodeHit
  · right
    by_cases bottom : level.val = 0
    · rw [if_pos bottom] at other ⊢
      have source := secret_point privateAnswers graph base ⟨level, tree, side, 0⟩
      rw [bottom] at source
      rw [source] at other
      exact (collision_public _ _ _ 2 _ _ _ _ _ _ _ (by decide) (by decide)).mp other
    · rw [if_neg bottom] at other ⊢
      rcases other with leafHit | ⟨chain, offset, within, chainHit⟩
      · left
        have endpoints : endpoint (hash privateAnswers graph base) 0 level.val tree.toNat side =
            fun chain => truncate (graph (.chain ⟨level, tree, side, chain⟩ 6)) := by
          funext chain
          exact completed_endpoint privateAnswers graph base ⟨level, tree, side, chain⟩
        rw [endpoints] at leafHit
        simp only [chainHash_public] at leafHit
        exact (collision_public _ _ _ 3 _ _ _ _ _ _ _ (by decide) (by decide)).mp leafHit
      · right
        refine ⟨chain, offset, within, ?_⟩
        have point := completed_walk privateAnswers graph base ⟨level, tree, side, chain⟩
          ⟨(digit message chain).val + offset, by have := (digit message chain).isLt; omega⟩
        rw [point] at chainHit
        simp only [chainHash_public] at chainHit
        exact (collision_public _ _ _ 2 _ _ _ _ _ _ _ (by decide) (by decide)).mp chainHit

end SigGolfCandidate.Hypertree.SecurityGraphCollision
