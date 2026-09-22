import SigGolfCandidate.Hypertree.SecurityGraphState

namespace SigGolfCandidate.Hypertree.SecurityGraphState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphReference SecurityGraphIdeal SecurityGraphSigner SecurityGraphOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

@[simp] theorem execute_signChain (privateAnswers : PrivateTable) (labels : Labels)
    (address : ChainAddress) (message : Digest) :
    execute privateAnswers labels (SecurityIdealSign.signChain address message) =
      pure (chainPoint privateAnswers labels address (digit message address.chain),
        truncate (labels (.chain address 6))) := by
  have digitBound : (digit message address.chain).val ≤ 7 := by
    have := (digit message address.chain).isLt; omega
  simp only [SecurityIdealSign.signChain, execute_bind, execute_secret, pure_bind, execute_public]
  change (publicExecute privateAnswers labels (SecurityReference.walk
    (SecurityReference.chainHash address.level.val address.tree.toNat address.side address.chain)
    0 (digit message address.chain).val (chainPoint privateAnswers labels address ⟨0, by decide⟩)) >>= _) = _
  rw [walk_points privateAnswers labels address 0 _ (by omega), pure_bind]
  simp only [Nat.zero_add]
  rw [walk_points privateAnswers labels address _ _ (by omega), pure_bind, execute_pure]
  have total : (digit message address.chain).val + (7 - (digit message address.chain).val) = 7 := by omega
  simp only [total, chainPoint, Nat.reduceEqDiff, ↓reduceDIte, Nat.reduceSub]
  rfl

/-- All honest layer-signing operations are canonical graph reads, so their
entire state computation is pure, including the sibling tree computation. -/
@[simp] theorem execute_signLayer (privateAnswers : PrivateTable) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) :
    execute privateAnswers labels (SecurityIdealSign.signLayerWithRoot level tree side message) =
      pure (layer privateAnswers labels level tree side message, truncate (labels (.node level tree))) := by
  by_cases bottom : level.val = 0
  · have current : publicExecute privateAnswers labels
        (SecurityReference.chainHash level.val tree.toNat side 0 0
          (truncate (privateAnswers (.chain ⟨level, tree, side, 0⟩)))) =
        pure (leafLabel labels level tree side) := by
      simpa [leafLabel, bottom, chainPoint] using
        chain_step privateAnswers labels ⟨level, tree, side, 0⟩ 0
    simp only [SecurityIdealSign.signLayerWithRoot, if_pos bottom, execute_bind,
      execute_secret, pure_bind, execute_public, current, execute_leafRoot]
    cases side <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        node_label, pure_bind, execute_pure, layer, if_pos bottom, chainPoint, Fin.val_zero, ↓reduceDIte]
  · have current : publicExecute privateAnswers labels
        (SecurityReference.compressLeaf level.val tree.toNat side
          (fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)))) =
        pure (leafLabel labels level tree side) := by
      simpa only [leafLabel, if_neg bottom] using compress_leaf privateAnswers labels level tree side
    simp only [SecurityIdealSign.signLayerWithRoot, if_neg bottom, execute_bind]
    rw [execute_sequenceFin privateAnswers labels 46 _
      (fun chain => (chainPoint privateAnswers labels ⟨level, tree, side, chain⟩ (digit message chain),
        truncate (labels (.chain ⟨level, tree, side, chain⟩ 6))))
      (fun chain => execute_signChain privateAnswers labels ⟨level, tree, side, chain⟩ message), pure_bind]
    simp only [execute_public, current, pure_bind, execute_leafRoot]
    cases side <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        node_label, pure_bind, execute_pure, layer, if_neg bottom]

@[simp] theorem execute_signUpper (privateAnswers : PrivateTable) (labels : Labels)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    execute privateAnswers labels (SecurityIdealSign.signUpper count level index hl hi message) =
      pure (upperLayers privateAnswers labels count level index hl hi message) := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [SecurityIdealSign.signUpper, execute_bind, execute_pure, execute_signLayer,
      pure_bind, ih, upperLayers]

/-- H5 is outside the canonical graph for every public key, message and nonce. -/
theorem canonical_index (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) (r : Bytes 32) :
    canonical privateAnswers labels (SecurityRandomOracle.indexInput pk message r) = none := by
  rw [canonical_eq_cache]
  have outside : ∀ position ∈ SecurityGraphOrder.positions,
      SecurityRandomOracle.indexInput pk message r ≠ position.input privateAnswers labels := by
    intro position _ same
    have equal := same.symm
    change position.address.input (position.payload privateAnswers labels) =
      (⟨5, 0, 0, 0, 0, 0⟩ : Address).input (bytes pk ++ bytes message ++ bytes r) at equal
    have tag := congrArg Address.tag (Address.eq_of_input_eq equal)
    cases position <;> cases tag
  rw [SecurityGraphQuery.graphCache_outside privateAnswers SecurityGraphOrder.positions labels ∅ _ outside]
  rfl

@[simp] theorem execute_randomizer (privateAnswers : PrivateTable) (labels : Labels) (message : Message) :
    execute privateAnswers labels (SecurityIdealSign.randomizer message) =
      pure (privateAnswers (.randomizer message)) := by
  simp only [execute, SecurityIdealSign.randomizer, splitImplementation, QueryImpl.add_eq_hAdd,
    QueryImpl.simulateQ_add_liftM_query_left]

@[simp] theorem publicExecute_index (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) (r : Bytes 32) :
    publicExecute privateAnswers labels (liftM (HashSpec.query (SecurityRandomOracle.indexInput pk message r))) =
      randomOracle (SecurityRandomOracle.indexInput pk message r) := by
  simp only [publicExecute, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, publicOracle, canonical_index]

/-- The nonce is a private-table read; only the H5 message-index query touches the residual oracle. -/
theorem execute_randomizedIndex (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) :
    execute privateAnswers labels (SecurityIdealSign.randomizedIndex pk message) = (do
      let answer ← randomOracle (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))
      pure (privateAnswers (.randomizer message), answer.extractLsb' 0 160)) := by
  simp only [SecurityIdealSign.randomizedIndex, execute_bind, execute_randomizer, pure_bind,
    execute_public, publicExecute_index, execute_pure]

/-- Full signing reduces to one residual H5 query followed by direct graph-coordinate serialization. -/
theorem execute_signCompact (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) :
    execute privateAnswers labels (SecurityIdealSign.signCompact pk message) = (do
      let answer ← randomOracle (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))
      pure (signature privateAnswers labels (privateAnswers (.randomizer message)) (answer.extractLsb' 0 160))) := by
  simp only [SecurityIdealSign.signCompact, execute_bind, execute_randomizedIndex, bind_assoc,
    pure_bind, execute_signLayer, execute_signUpper, execute_pure]
  rfl

/-- Exact resulting residual cache: it is precisely the cache after the single H5 call. -/
theorem signCompact_run (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) (cache : QueryCache HashSpec) :
    (execute privateAnswers labels (SecurityIdealSign.signCompact pk message)).run cache =
      (fun result => (signature privateAnswers labels (privateAnswers (.randomizer message))
        (result.1.extractLsb' 0 160), result.2)) <$>
      (randomOracle (spec := HashSpec)
        (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))).run cache := by
  rw [execute_signCompact]
  simp only [StateT.run_bind, StateT.run_pure, map_eq_pure_bind]

end SigGolfCandidate.Hypertree.SecurityGraphState
