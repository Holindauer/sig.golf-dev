import SigGolfCandidate.Hypertree.SecurityGraphIdeal

namespace SigGolfCandidate.Hypertree.SecurityGraphSigner
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphReference SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def answers (privateAnswers : PrivateTable) (hash : Hash) : QueryImpl SplitWorld Id :=
  QueryImpl.add (m := Id) (spec₁ := SecretSpec) (spec₂ := HashSpec) privateAnswers hash

@[simp] theorem eval_public {α : Type} (privateAnswers : PrivateTable) (hash : Hash)
    (program : OracleComp HashSpec α) :
    evalWithAnswerFn (answers privateAnswers hash) (SecurityIdealKeygen.publicCall program) =
      evalWithAnswerFn hash program := by
  simpa only [evalWithAnswerFn, answers, SecurityIdealKeygen.publicCall, QueryImpl.add_eq_hAdd] using
    QueryImpl.simulateQ_add_liftComp_right
    ((fun slot => privateAnswers slot) : QueryImpl SecretSpec Id) hash program

@[simp] theorem eval_secret (privateAnswers : PrivateTable) (hash : Hash) (address : ChainAddress) :
    evalWithAnswerFn (answers privateAnswers hash) (SecurityIdealKeygen.secret address) =
      truncate (privateAnswers (.chain address)) := by
  change truncate (privateAnswers (.chain address)) = _
  rfl

theorem eval_sequenceFin {α : Type} (privateAnswers : PrivateTable) (hash : Hash) (n : Nat)
    (body : Fin n → OracleComp SplitWorld α) :
    evalWithAnswerFn (answers privateAnswers hash) (SecurityIdealKeygen.sequenceFin n body) =
      fun i => evalWithAnswerFn (answers privateAnswers hash) (body i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [SecurityIdealKeygen.sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Every public chain walk in the independent-source signer traverses precisely
the programmed graph points. -/
theorem walk_points (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (address : ChainAddress) (count : Nat) (bound : count ≤ 7) :
    walk (chainHash (programmed privateAnswers labels residual)
      address.level.val address.tree.toNat address.side address.chain) 0 count
      (truncate (privateAnswers (.chain address))) =
      chainPoint privateAnswers labels address ⟨count, by omega⟩ := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [walk_append _ 0 count 1]
    simp only [walk, Nat.zero_add]
    rw [ih (by omega)]
    have step := programmed_chain_step privateAnswers labels residual address ⟨count, by omega⟩
    simpa only [chainPoint, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel] using step

@[simp] theorem eval_endpoint (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (address : ChainAddress) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealKeygen.endpoint address) = truncate (labels (.chain address 6)) := by
  simp only [SecurityIdealKeygen.endpoint, evalWithAnswerFn_bind, eval_secret, eval_public,
    SecurityReference.eval_walk, SecurityReference.eval_chainHash]
  exact walk_points privateAnswers labels residual address 7 (by decide)

/-- Actual independent-source WOTS signing returns one selected point and the
canonical endpoint, with no dependence on other interior chain labels. -/
theorem eval_signChain (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (address : ChainAddress) (message : Digest) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.signChain address message) =
      (chainPoint privateAnswers labels address (digit message address.chain),
        truncate (labels (.chain address 6))) := by
  simp only [SecurityIdealSign.signChain, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_secret, eval_public, SecurityReference.eval_walk, SecurityReference.eval_chainHash]
  have total := walk_append
    (chainHash (programmed privateAnswers labels residual) address.level.val address.tree.toNat
      address.side address.chain) 0 (digit message address.chain).val
      (7 - (digit message address.chain).val) (truncate (privateAnswers (.chain address)))
  have digitBound : (digit message address.chain).val ≤ 7 := by have := (digit message address.chain).isLt; omega
  have totalCount : (digit message address.chain).val + (7 - (digit message address.chain).val) = 7 := by omega
  simp only [Nat.zero_add, totalCount] at total
  rw [← total, walk_points privateAnswers labels residual address _ digitBound]
  exact congrArg (fun last => (chainPoint privateAnswers labels address (digit message address.chain), last))
    (walk_points privateAnswers labels residual address 7 (by decide))

/-- The signer needs only public endpoint/leaf labels for the sibling subtree. -/
theorem eval_leafRoot (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealKeygen.leafRoot level tree side) = leafLabel labels level tree side := by
  by_cases bottom : level.val = 0
  · simp only [SecurityIdealKeygen.leafRoot, evalWithAnswerFn_bind,
      eval_secret, eval_public, SecurityReference.eval_chainHash, leafLabel, if_pos bottom]
    exact programmed_chain_step privateAnswers labels residual ⟨level, tree, side, 0⟩ 0
  · simp only [SecurityIdealKeygen.leafRoot, evalWithAnswerFn_bind,
      eval_sequenceFin, eval_endpoint, eval_public, SecurityReference.eval_compressLeaf,
      leafLabel, if_neg bottom]
    change truncate (programmed privateAnswers labels residual
      ((Position.leaf level tree side).input privateAnswers labels)) = _
    rw [programmed_graph]

/-- All canonical tree roots are designated independent node labels. -/
theorem eval_treeRoot (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (level : Fin 160) (tree : BitVec 192) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealKeygen.treeRoot level tree) = truncate (labels (.node level tree)) := by
  simp only [SecurityIdealKeygen.treeRoot, evalWithAnswerFn_bind, eval_leafRoot,
    eval_public, SecurityReference.eval_node]
  change truncate (programmed privateAnswers labels residual
    ((Position.node level tree).input privateAnswers labels)) = _
  rw [programmed_graph]

theorem eval_keygen (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      SecurityIdealKeygen.keygen = truncate (labels (.node 159 0)) :=
  eval_treeRoot privateAnswers labels residual 159 0

/-- The exact fields revealed by an actual ideal layer signature. At the bottom
only chain zero is serialized; an upper layer reveals its digit-selected points. -/
def layer (privateAnswers : PrivateTable) (labels : Labels) (level : Fin 160)
    (tree : BitVec 192) (side : Bool) (message : Digest) : LayerSignature :=
  ⟨if level.val = 0 then
      fun i => if i = 0 then chainPoint privateAnswers labels ⟨level, tree, side, 0⟩ 0 else 0
    else fun i => chainPoint privateAnswers labels ⟨level, tree, side, i⟩ (digit message i),
    leafLabel labels level tree (!side)⟩

theorem compress_leaf (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    compressLeaf (programmed privateAnswers labels residual) level.val tree.toNat side
      (fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6))) =
      truncate (labels (.leaf level tree side)) := by
  change truncate (programmed privateAnswers labels residual
    ((Position.leaf level tree side).input privateAnswers labels)) = _
  rw [programmed_graph]

theorem node_label (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (level : Fin 160) (tree : BitVec 192) :
    node (programmed privateAnswers labels residual) level.val tree.toNat
      (leafLabel labels level tree false) (leafLabel labels level tree true) =
      truncate (labels (.node level tree)) := by
  change truncate (programmed privateAnswers labels residual
    ((Position.node level tree).input privateAnswers labels)) = _
  rw [programmed_graph]

/-- Exact whole-layer signing, including the child-root message passed upward.
This is the actual monadic signer, not an abstract signature interface. -/
theorem eval_signLayer (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.signLayerWithRoot level tree side message) =
      (layer privateAnswers labels level tree side message, truncate (labels (.node level tree))) := by
  by_cases bottom : level.val = 0
  · have current : chainHash (programmed privateAnswers labels residual) level.val tree.toNat side 0 0
        (truncate (privateAnswers (.chain ⟨level, tree, side, 0⟩))) = leafLabel labels level tree side := by
      simpa only [leafLabel, if_pos bottom, chainPoint, Fin.val_zero, ↓reduceDIte] using
        programmed_chain_step privateAnswers labels residual ⟨level, tree, side, 0⟩ 0
    simp only [SecurityIdealSign.signLayerWithRoot, if_pos bottom, evalWithAnswerFn_bind,
      evalWithAnswerFn_pure, eval_secret, eval_public, SecurityReference.eval_chainHash,
      current, eval_leafRoot]
    cases side <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        SecurityReference.eval_node, node_label, layer, if_pos bottom, chainPoint, Fin.val_zero,
        ↓reduceDIte]
  · have current : compressLeaf (programmed privateAnswers labels residual) level.val tree.toNat side
        (fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6))) =
          leafLabel labels level tree side := by
      simpa only [leafLabel, if_neg bottom] using compress_leaf privateAnswers labels residual level tree side
    simp only [SecurityIdealSign.signLayerWithRoot, if_neg bottom, evalWithAnswerFn_bind,
      evalWithAnswerFn_pure, eval_sequenceFin, eval_signChain, eval_public,
      SecurityReference.eval_compressLeaf, current, eval_leafRoot]
    cases side <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        SecurityReference.eval_node, node_label, layer, if_neg bottom]


/-- Honest message-index hashing is outside every planted graph address. -/
theorem programmed_index (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (pk : PublicKey) (message : Message) (r : Bytes 32) :
    programmed privateAnswers labels residual (SecurityRandomOracle.indexInput pk message r) =
      residual (SecurityRandomOracle.indexInput pk message r) := by
  unfold programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    change position.address.input (position.payload privateAnswers labels) =
      (⟨5, 0, 0, 0, 0, 0⟩ : Address).input (bytes pk ++ bytes message ++ bytes r) at same
    have tag := congrArg Address.tag (Address.eq_of_input_eq same)
    cases position <;> cases tag
  next absent => rfl

theorem eval_randomizedIndex (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (pk : PublicKey) (message : Message) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.randomizedIndex pk message) =
      (privateAnswers (.randomizer message),
        (residual (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))).extractLsb' 0 160) := by
  have nonce : evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.randomizer message) = privateAnswers (.randomizer message) := rfl
  simp only [SecurityIdealSign.randomizedIndex, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    nonce, eval_public]
  change (privateAnswers (.randomizer message),
    (programmed privateAnswers labels residual (SecurityRandomOracle.indexInput pk message
      (privateAnswers (.randomizer message)))).extractLsb' 0 160) = _
  rw [programmed_index]

/-- Canonical upper signatures as direct graph-coordinate reads. After the first
layer, every WOTS message is a public node label independent of interior points. -/
def upperLayers (privateAnswers : PrivateTable) (labels : Labels) :
    (count level index : Nat) → count + level ≤ 160 → index < 2 ^ 192 →
      Digest → List LayerSignature
  | 0, _, _, _, _, _ => []
  | count + 1, level, index, hl, hi, message =>
      let atLevel : Fin 160 := ⟨level, by omega⟩
      let tree := BitVec.ofNat 192 (index / 2)
      layer privateAnswers labels atLevel tree (index % 2 == 1) message ::
        upperLayers privateAnswers labels count (level + 1) (index / 2) (by omega)
          (lt_of_le_of_lt (Nat.div_le_self ..) hi) (truncate (labels (.node atLevel tree)))

theorem eval_signUpper (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.signUpper count level index hl hi message) =
      upperLayers privateAnswers labels count level index hl hi message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [SecurityIdealSign.signUpper, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      eval_signLayer, ih, upperLayers]

private theorem index_bound (index : BitVec 160) : index.toNat / 2 < 2 ^ 192 := by
  have bound : (2 : Nat) ^ 160 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
  exact lt_of_le_of_lt (Nat.div_le_self ..) (lt_of_lt_of_le index.isLt bound)

/-- All compact signature fields as explicit graph-coordinate reveals. -/
def signature (privateAnswers : PrivateTable) (labels : Labels) (r : Bytes 32)
    (index : BitVec 160) : SignatureEncoding.Compact :=
  let tree := BitVec.ofNat 192 (index.toNat / 2)
  let side := index.toNat % 2 == 1
  ⟨r, chainPoint privateAnswers labels ⟨0, tree, side, 0⟩ 0,
    leafLabel labels 0 tree (!side),
    upperLayers privateAnswers labels 159 1 (index.toNat / 2) (by decide) (index_bound index)
      (truncate (labels (.node 0 tree)))⟩

/-- The actual full ideal signing program has exactly this graph-coordinate
signature, with its secret deterministic nonce and residual-oracle index. -/
theorem eval_signCompact (privateAnswers : PrivateTable) (labels : Labels) (residual : Hash)
    (pk : PublicKey) (message : Message) :
    evalWithAnswerFn (answers privateAnswers (programmed privateAnswers labels residual))
      (SecurityIdealSign.signCompact pk message) =
      signature privateAnswers labels (privateAnswers (.randomizer message))
        ((residual (SecurityRandomOracle.indexInput pk message
          (privateAnswers (.randomizer message)))).extractLsb' 0 160) := by
  simp only [SecurityIdealSign.signCompact, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_randomizedIndex, eval_signLayer, eval_signUpper]
  rfl


end SigGolfCandidate.Hypertree.SecurityGraphSigner
