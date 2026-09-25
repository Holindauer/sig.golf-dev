import SigGolfCandidate.Hypertree.SecurityGraphOracle
import SigGolfCandidate.Hypertree.SecurityGraphSigner

namespace SigGolfCandidate.Hypertree.SecurityGraphState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphReference SecurityGraphIdeal SecurityGraphSigner SecurityGraphOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev ResidualM := StateT (QueryCache HashSpec) ProbComp

noncomputable def splitImplementation (privateAnswers : PrivateTable) (labels : Labels) :
    QueryImpl SplitWorld ResidualM :=
  QueryImpl.add (fun slot => pure (privateAnswers slot)) (publicOracle privateAnswers labels)

noncomputable def execute {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp SplitWorld α) : ResidualM α :=
  simulateQ (splitImplementation privateAnswers labels) program

noncomputable def publicExecute {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp HashSpec α) : ResidualM α :=
  simulateQ (publicOracle privateAnswers labels) program

@[simp] theorem execute_pure {α : Type} (privateAnswers : PrivateTable) (labels : Labels) (value : α) :
    execute privateAnswers labels (pure value) = pure value := by simp [execute]

@[simp] theorem execute_bind {α β : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp SplitWorld α) (next : α → OracleComp SplitWorld β) :
    execute privateAnswers labels (program >>= next) =
      execute privateAnswers labels program >>= fun value => execute privateAnswers labels (next value) := by
  simp [execute]

@[simp] theorem publicExecute_pure {α : Type} (privateAnswers : PrivateTable) (labels : Labels) (value : α) :
    publicExecute privateAnswers labels (pure value) = pure value := by simp [publicExecute]

@[simp] theorem publicExecute_bind {α β : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    publicExecute privateAnswers labels (program >>= next) =
      publicExecute privateAnswers labels program >>= fun value => publicExecute privateAnswers labels (next value) := by
  simp [publicExecute]

@[simp] theorem execute_public {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp HashSpec α) :
    execute privateAnswers labels (SecurityIdealKeygen.publicCall program) =
      publicExecute privateAnswers labels program := by
  simpa only [execute, publicExecute, splitImplementation, SecurityIdealKeygen.publicCall,
    QueryImpl.add_eq_hAdd] using QueryImpl.simulateQ_add_liftComp_right
    ((fun slot => pure (privateAnswers slot)) : QueryImpl SecretSpec ResidualM)
    (publicOracle privateAnswers labels) program

@[simp] theorem execute_secret (privateAnswers : PrivateTable) (labels : Labels) (address : ChainAddress) :
    execute privateAnswers labels (SecurityIdealKeygen.secret address) =
      pure (truncate (privateAnswers (.chain address))) := by
  simp only [execute, SecurityIdealKeygen.secret, simulateQ_map, splitImplementation, QueryImpl.add_eq_hAdd,
    QueryImpl.simulateQ_add_liftM_query_left, map_pure]

@[simp] theorem canonical_graph (privateAnswers : PrivateTable) (labels : Labels) (position : Position) :
    canonical privateAnswers labels (position.input privateAnswers labels) = some (labels position) := by
  rw [canonical_eq_cache]
  exact SecurityGraphQuery.graphCache_inside privateAnswers SecurityGraphOrder.positions labels ∅
    position (SecurityGraphOrder.positions_complete position)

@[simp] theorem publicExecute_graph (privateAnswers : PrivateTable) (labels : Labels) (position : Position) :
    publicExecute privateAnswers labels
      (liftM (HashSpec.query (position.input privateAnswers labels))) = pure (labels position) := by
  simp only [publicExecute, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, publicOracle, canonical_graph]

theorem chain_step (privateAnswers : PrivateTable) (labels : Labels)
    (address : ChainAddress) (step : Fin 7) :
    publicExecute privateAnswers labels
      (SecurityReference.chainHash address.level.val address.tree.toNat address.side address.chain step.val
        (chainPoint privateAnswers labels address ⟨step.val, by omega⟩)) =
      pure (chainPoint privateAnswers labels address step.succ) := by
  have input : SecurityReference.ask 2 address.level.val address.tree.toNat (sideNumber address.side)
      address.chain.val step.val (bytes (chainPoint privateAnswers labels address ⟨step.val, by omega⟩)) =
      (liftM (HashSpec.query ((Position.chain address step).input privateAnswers labels))) := rfl
  simp only [SecurityReference.chainHash, publicExecute, simulateQ_map]
  change truncate <$> publicExecute privateAnswers labels _ = _
  rw [input, publicExecute_graph, map_pure]
  simp [chainPoint]

/-- Canonical chain walks are pure state computations: no residual read or write. -/
theorem walk_points (privateAnswers : PrivateTable) (labels : Labels)
    (address : ChainAddress) (start count : Nat) (bound : start + count ≤ 7) :
    publicExecute privateAnswers labels
      (SecurityReference.walk (SecurityReference.chainHash address.level.val address.tree.toNat
        address.side address.chain) start count
        (chainPoint privateAnswers labels address ⟨start, by omega⟩)) =
      pure (chainPoint privateAnswers labels address ⟨start + count, by omega⟩) := by
  induction count generalizing start with
  | zero => simp only [SecurityReference.walk, publicExecute_pure, Nat.add_zero]
  | succ count ih =>
    simp only [SecurityReference.walk, publicExecute_bind]
    rw [chain_step privateAnswers labels address ⟨start, by omega⟩, pure_bind]
    have nextPoint : (⟨start, by omega⟩ : Fin 7).succ = (⟨start + 1, by omega⟩ : Fin 8) := Fin.ext rfl
    rw [nextPoint]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1) (by omega)

@[simp] theorem execute_endpoint (privateAnswers : PrivateTable) (labels : Labels) (address : ChainAddress) :
    execute privateAnswers labels (SecurityIdealKeygen.endpoint address) =
      pure (truncate (labels (.chain address 6))) := by
  simp only [SecurityIdealKeygen.endpoint, execute_bind, execute_secret, pure_bind, execute_public]
  exact walk_points privateAnswers labels address 0 7 (by decide)

/-- Pointwise pure bodies remain pure under the actual finite sequencing routine. -/
theorem execute_sequenceFin {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (n : Nat) (body : Fin n → OracleComp SplitWorld α) (values : Fin n → α)
    (bodyPure : ∀ i, execute privateAnswers labels (body i) = pure (values i)) :
    execute privateAnswers labels (SecurityIdealKeygen.sequenceFin n body) = pure values := by
  induction n with
  | zero =>
    have same : values = Fin.elim0 := funext fun i => Fin.elim0 i
    subst values
    rfl
  | succ n ih =>
    simp only [SecurityIdealKeygen.sequenceFin, execute_bind, bodyPure, pure_bind]
    rw [ih _ (fun i => values i.succ) (fun i => bodyPure i.succ), pure_bind, execute_pure]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem compress_leaf (privateAnswers : PrivateTable) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    publicExecute privateAnswers labels (SecurityReference.compressLeaf level.val tree.toNat side
      (fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)))) =
      pure (truncate (labels (.leaf level tree side))) := by
  simp only [SecurityReference.compressLeaf, publicExecute, simulateQ_map]
  change truncate <$> publicExecute privateAnswers labels
    (liftM (HashSpec.query ((Position.leaf level tree side).input privateAnswers labels))) = _
  rw [publicExecute_graph, map_pure]

theorem node_label (privateAnswers : PrivateTable) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) :
    publicExecute privateAnswers labels (SecurityReference.node level.val tree.toNat
      (leafLabel labels level tree false) (leafLabel labels level tree true)) =
      pure (truncate (labels (.node level tree))) := by
  simp only [SecurityReference.node, publicExecute, simulateQ_map]
  change truncate <$> publicExecute privateAnswers labels
    (liftM (HashSpec.query ((Position.node level tree).input privateAnswers labels))) = _
  rw [publicExecute_graph, map_pure]

@[simp] theorem execute_leafRoot (privateAnswers : PrivateTable) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    execute privateAnswers labels (SecurityIdealKeygen.leafRoot level tree side) =
      pure (leafLabel labels level tree side) := by
  by_cases bottom : level.val = 0
  · simp only [SecurityIdealKeygen.leafRoot, if_pos bottom, execute_bind, execute_secret,
      pure_bind, execute_public, leafLabel]
    exact chain_step privateAnswers labels ⟨level, tree, side, 0⟩ 0
  · simp only [SecurityIdealKeygen.leafRoot, if_neg bottom, execute_bind]
    rw [execute_sequenceFin privateAnswers labels 46 _
      (fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)))
      (fun chain => execute_endpoint privateAnswers labels ⟨level, tree, side, chain⟩), pure_bind,
      execute_public, compress_leaf]
    simp only [leafLabel, if_neg bottom]

@[simp] theorem execute_treeRoot (privateAnswers : PrivateTable) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) :
    execute privateAnswers labels (SecurityIdealKeygen.treeRoot level tree) =
      pure (truncate (labels (.node level tree))) := by
  simp only [SecurityIdealKeygen.treeRoot, execute_bind, execute_leafRoot, pure_bind,
    execute_public, node_label]

/-- Actual key generation returns the planted root and leaves any residual cache unchanged. -/
theorem keygen_run (privateAnswers : PrivateTable) (labels : Labels) (cache : QueryCache HashSpec) :
    (execute privateAnswers labels SecurityIdealKeygen.keygen).run cache =
      pure (truncate (labels (.node 159 0)), cache) := by
  rw [SecurityIdealKeygen.keygen, execute_treeRoot]
  rfl

end SigGolfCandidate.Hypertree.SecurityGraphState
