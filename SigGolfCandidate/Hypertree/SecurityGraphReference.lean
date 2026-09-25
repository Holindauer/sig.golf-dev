import SigGolfCandidate.Hypertree.SecurityGraph

namespace SigGolfCandidate.Hypertree.SecurityGraphReference
open SigGolf Reference SecurityRandomOracle SecurityDerivation SecuritySeparation SecurityGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def derived (residual : Hash) (secretKey : SecretKey) : Slot → BitVec 256 :=
  fun slot => residual (SecurityDerivation.input secretKey slot)

/-- One full output is planted at each separated canonical graph input. -/
noncomputable def programmed (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash) : Hash :=
  fun query => if found : ∃ position, position.input privateAnswers labels = query
    then labels found.choose else residual query

theorem programmed_graph (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (position : Position) :
    programmed privateAnswers labels residual (position.input privateAnswers labels) = labels position := by
  unfold programmed
  split
  next found =>
    have same : found.choose = position := by
      by_contra different
      exact Position.input_separated privateAnswers _ _ different labels labels found.choose_spec
    rw [same]
  next absent => exact False.elim (absent ⟨position, rfl⟩)

theorem graphInput_not_secretKeyEligible (privateAnswers : Slot → BitVec 256) (position : Position)
    (labels : Labels) : ¬SecretKeyEligible (position.input privateAnswers labels) := by
  cases position with
  | chain address step =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 2 _ _ _ _ _ _ (by decide) (by decide)
  | leaf level tree side =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 3 _ _ _ _ _ _ (by decide) (by decide)
  | node level tree =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 4 _ _ _ _ _ _ (by decide) (by decide)

/-- Planting public graph labels cannot change either secret-chain derivations or
message-randomizer derivations at any secret key. -/
theorem programmed_private (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (secretKey : SecretKey) (slot : Slot) :
    programmed privateAnswers labels residual (SecurityDerivation.input secretKey slot) =
      residual (SecurityDerivation.input secretKey slot) := by
  unfold programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    exact False.elim (graphInput_not_secretKeyEligible privateAnswers position labels (same ▸ secretKeyEligible_input secretKey slot))
  next absent => rfl

/-- The signer secret is unchanged by graph programming, at the actual reference input. -/
theorem programmed_secret (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress) :
    secret (programmed (derived residual secretKey) labels residual) secretKey address.level.val address.tree.toNat
      address.side address.chain = truncate (derived residual secretKey (.chain address)) := by
  change truncate (programmed (derived residual secretKey) labels residual
    (SecurityDerivation.input secretKey (.chain address))) = _
  rw [programmed_private]
  rfl

/-- Canonical chain points: private source at zero, independent graph label thereafter. -/
def chainPoint (privateAnswers : Slot → BitVec 256) (labels : Labels) (address : ChainAddress)
    (point : Fin 8) : Digest :=
  if zero : point.val = 0 then truncate (privateAnswers (.chain address))
  else truncate (labels (.chain address ⟨point.val - 1, by omega⟩))

theorem programmed_chain_step (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (address : ChainAddress) (step : Fin 7) :
    chainHash (programmed privateAnswers labels residual) address.level.val address.tree.toNat
      address.side address.chain step.val (chainPoint privateAnswers labels address ⟨step.val, by omega⟩) =
        truncate (labels (.chain address step)) := by
  change truncate (programmed privateAnswers labels residual
    ((Position.chain address step).input privateAnswers labels)) = _
  rw [programmed_graph]

/-- Every actual reference walk through seven planted steps reads the designated
independent point; this includes every possible WOTS signing digit. -/
theorem programmed_walk (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress)
    (count : Nat) (bound : count ≤ 7) :
    walk (chainHash (programmed (derived residual secretKey) labels residual)
      address.level.val address.tree.toNat address.side address.chain) 0 count
      (secret (programmed (derived residual secretKey) labels residual) secretKey address.level.val
        address.tree.toNat address.side address.chain) =
      chainPoint (derived residual secretKey) labels address ⟨count, by omega⟩ := by
  induction count with
  | zero => simpa only [walk, chainPoint, ↓reduceDIte] using programmed_secret residual secretKey labels address
  | succ count ih =>
    rw [walk_append _ 0 count 1]
    simp only [walk, Nat.zero_add]
    rw [ih (by omega)]
    have step := programmed_chain_step (derived residual secretKey) labels residual address ⟨count, by omega⟩
    simpa only [chainPoint, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel] using step

/-- The exact reference WOTS endpoint is the final canonical chain label. -/
theorem programmed_endpoint (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress) :
    endpoint (programmed (derived residual secretKey) labels residual) secretKey address.level.val
      address.tree.toNat address.side address.chain = truncate (labels (.chain address 6)) := by
  exact programmed_walk residual secretKey labels address 7 (by decide)

def leafLabel (labels : Labels) (level : Fin 160) (tree : BitVec 192) (side : Bool) : Digest :=
  if level.val = 0 then truncate (labels (.chain ⟨level, tree, side, 0⟩ 0))
  else truncate (labels (.leaf level tree side))

/-- Actual binary-tree leaves recover the sampled graph labels at both the
bottom preimage layer and all upper WOTS layers. -/
theorem programmed_leafRoot (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    leafRoot (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side =
      leafLabel labels level tree side := by
  by_cases bottom : level.val = 0
  · simp only [leafRoot, leafLabel, if_pos bottom]
    rw [programmed_secret residual secretKey labels ⟨level, tree, side, 0⟩]
    exact programmed_chain_step (derived residual secretKey) labels residual ⟨level, tree, side, 0⟩ 0
  · simp only [leafRoot, leafLabel, if_neg bottom]
    have endpoints : endpoint (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side =
        fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)) := by
      funext chain
      exact programmed_endpoint residual secretKey labels ⟨level, tree, side, chain⟩
    rw [endpoints]
    change truncate (programmed (derived residual secretKey) labels residual
      ((Position.leaf level tree side).input (derived residual secretKey) labels)) = _
    rw [programmed_graph]

/-- The actual reference public key and every child-tree message are designated
node labels. The probability proof can therefore identify their independence from
WOTS interior points without treating reference hashing as an independent oracle. -/
theorem programmed_treeRoot (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) :
    treeRoot (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat =
      truncate (labels (.node level tree)) := by
  rw [treeRoot, programmed_leafRoot, programmed_leafRoot]
  change truncate (programmed (derived residual secretKey) labels residual
    ((Position.node level tree).input (derived residual secretKey) labels)) = _
  rw [programmed_graph]

/-- Signing reveals exactly the canonical point selected by each WOTS digit. -/
theorem programmed_sign_fragment (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) (chain : Chain) :
    (signLayer (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side message).values chain =
      if level.val = 0 then chainPoint (derived residual secretKey) labels ⟨level, tree, side, chain⟩ 0
      else chainPoint (derived residual secretKey) labels ⟨level, tree, side, chain⟩ (digit message chain) := by
  by_cases bottom : level.val = 0
  · simp only [signLayer, if_pos bottom]
    exact programmed_secret residual secretKey labels ⟨level, tree, side, chain⟩
  · simp only [signLayer, if_neg bottom]
    exact programmed_walk residual secretKey labels ⟨level, tree, side, chain⟩ (digit message chain).val (by omega)

end SigGolfCandidate.Hypertree.SecurityGraphReference
