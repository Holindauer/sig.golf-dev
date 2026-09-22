import SigGolfCandidate.Hypertree.SecurityGraphPassive

namespace SigGolfCandidate.Hypertree.SecurityGraphFactor
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphIdeal SecurityGraphFrontier SecurityGraphPassive
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The labels outside chains: leaf and binary-node outputs. -/
inductive Metadata where
  | leaf (level : Fin 160) (tree : BitVec 192) (side : Bool)
  | node (level : Fin 160) (tree : BitVec 192)
  deriving DecidableEq

def Metadata.position : Metadata → Position
  | .leaf level tree side => .leaf level tree side
  | .node level tree => .node level tree

theorem Metadata.position_injective : Function.Injective Metadata.position := by
  intro first second same
  cases first <;> cases second <;> simp_all [Metadata.position]

instance : Finite Metadata := Finite.of_injective _ Metadata.position_injective
noncomputable instance : Fintype Metadata := Fintype.ofFinite Metadata
abbrev NonceTable := Message → BitVec 256
abbrev MetadataTable := Metadata → BitVec 256
noncomputable instance : SampleableType MetadataTable := SampleableType.ofFintype MetadataTable
abbrev Factors := PointTable × (NonceTable × MetadataTable)

/-- Full-width points, before the truncation used in signatures. -/
def points (privateAnswers : PrivateTable) (labels : Labels) : PointTable :=
  fun point => if zero : point.2.val = 0 then privateAnswers (.chain point.1)
    else labels (.chain point.1 ⟨point.2.val - 1, by omega⟩)

def factor (tables : PrivateTable × Labels) : Factors :=
  (points tables.1 tables.2, (fun message => tables.1 (.randomizer message),
    fun metadata => tables.2 metadata.position))

def privateTable (factors : Factors) : PrivateTable
  | .chain address => factors.1 (address, 0)
  | .randomizer message => factors.2.1 message

def labels (factors : Factors) : Labels
  | .chain address step => factors.1 (address, step.succ)
  | .leaf level tree side => factors.2.2 (.leaf level tree side)
  | .node level tree => factors.2.2 (.node level tree)

def assemble (factors : Factors) : PrivateTable × Labels := (privateTable factors, labels factors)

@[simp] theorem points_zero (privateAnswers : PrivateTable) (graph : Labels) (address : ChainAddress) :
    points privateAnswers graph (address, 0) = privateAnswers (.chain address) := by
  simp [points]

@[simp] theorem points_succ (privateAnswers : PrivateTable) (graph : Labels)
    (address : ChainAddress) (step : Fin 7) :
    points privateAnswers graph (address, step.succ) = graph (.chain address step) := by
  simp [points]

@[simp] theorem assemble_factor (tables : PrivateTable × Labels) : assemble (factor tables) = tables := by
  apply Prod.ext
  · funext slot
    cases slot <;> simp [assemble, privateTable, factor]
  · funext position
    cases position <;> simp [assemble, labels, factor, Metadata.position]

@[simp] theorem factor_assemble (factors : Factors) : factor (assemble factors) = factors := by
  apply Prod.ext
  · funext point
    rcases point with ⟨address, point⟩
    refine Fin.cases ?_ (fun step => ?_) point
    · simp [factor, assemble, privateTable]
    · simp [factor, assemble, labels]
  · apply Prod.ext
    · funext message
      rfl
    · funext metadata
      cases metadata <;> rfl

/-- An explicit coordinate bijection; no sampled value is discarded. -/
def equivalence : (PrivateTable × Labels) ≃ Factors where
  toFun := factor
  invFun := assemble
  left_inv := assemble_factor
  right_inv := factor_assemble

@[simp] theorem factor_source (tables : PrivateTable × Labels) (address : ChainAddress) :
    (factor tables).1 (address, 0) = tables.1 (.chain address) := points_zero tables.1 tables.2 address

@[simp] theorem factor_chain (tables : PrivateTable × Labels) (address : ChainAddress) (step : Fin 7) :
    (factor tables).1 (address, step.succ) = tables.2 (.chain address step) := points_succ tables.1 tables.2 address step

@[simp] theorem factor_nonce (tables : PrivateTable × Labels) (message : Message) :
    (factor tables).2.1 message = tables.1 (.randomizer message) := rfl

@[simp] theorem factor_leaf (tables : PrivateTable × Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    (factor tables).2.2 (.leaf level tree side) = tables.2 (.leaf level tree side) := rfl

@[simp] theorem factor_node (tables : PrivateTable × Labels) (level : Fin 160) (tree : BitVec 192) :
    (factor tables).2.2 (.node level tree) = tables.2 (.node level tree) := rfl

theorem chainPoint_eq (privateAnswers : PrivateTable) (graph : Labels) (address : ChainAddress)
    (point : Fin 8) : SecurityGraphReference.chainPoint privateAnswers graph address point =
      truncate (points privateAnswers graph (address, point)) := by
  unfold SecurityGraphReference.chainPoint points
  split <;> rfl

@[simp] theorem privateTable_source (factors : Factors) (address : ChainAddress) :
    privateTable factors (.chain address) = factors.1 (address, 0) := rfl

@[simp] theorem privateTable_nonce (factors : Factors) (message : Message) :
    privateTable factors (.randomizer message) = factors.2.1 message := rfl

@[simp] theorem labels_chain (factors : Factors) (address : ChainAddress) (step : Fin 7) :
    labels factors (.chain address step) = factors.1 (address, step.succ) := rfl

@[simp] theorem labels_leaf (factors : Factors) (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    labels factors (.leaf level tree side) = factors.2.2 (.leaf level tree side) := rfl

@[simp] theorem labels_node (factors : Factors) (level : Fin 160) (tree : BitVec 192) :
    labels factors (.node level tree) = factors.2.2 (.node level tree) := rfl

@[simp] theorem assembled_chainPoint (factors : Factors) (address : ChainAddress) (point : Fin 8) :
    SecurityGraphReference.chainPoint (privateTable factors) (labels factors) address point =
      truncate (factors.1 (address, point)) := by
  rw [chainPoint_eq]
  have same := congrArg (fun data : Factors => data.1 (address, point)) (factor_assemble factors)
  exact congrArg truncate same

/-- Uniform graph coordinates become a uniform factor tuple under the bijection. -/
theorem uniform_factor :
    𝒮[factor <$> ($ᵗ (PrivateTable × Labels))] = 𝒮[$ᵗ Factors] :=
  evalSPMF_map_bijective_uniform_cross (PrivateTable × Labels) factor equivalence.bijective

private theorem uniform_pair (A B : Type) [SampleableType A] [SampleableType B] :
    ($ᵗ (A × B)) = (do let a ← $ᵗ A; let b ← $ᵗ B; pure (a, b)) := by
  change ((Prod.mk <$> ($ᵗ A)) <*> ($ᵗ B)) = _
  simp only [seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]

/-- Explicit independent product law for the three factor tables. -/
theorem independent_factors :
    𝒮[do
      let privateAnswers ← $ᵗ PrivateTable
      let graph ← $ᵗ Labels
      pure (factor (privateAnswers, graph))] =
    𝒮[do
      let pointTable ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      let metadata ← $ᵗ MetadataTable
      pure (pointTable, (nonces, metadata))] := by
  simpa only [uniform_pair, map_eq_pure_bind, bind_assoc, pure_bind] using uniform_factor

/-- The factorization is valid inside every randomized continuation. -/
theorem independent_bind {α : Type} (next : Factors → ProbComp α) :
    𝒮[do
      let privateAnswers ← $ᵗ PrivateTable
      let graph ← $ᵗ Labels
      next (factor (privateAnswers, graph))] =
    𝒮[do
      let pointTable ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      let metadata ← $ᵗ MetadataTable
      next (pointTable, (nonces, metadata))] := by
  calc
    _ = 𝒮[(do
      let privateAnswers ← $ᵗ PrivateTable
      let graph ← $ᵗ Labels
      pure (factor (privateAnswers, graph))) >>= next] := by simp only [bind_assoc, pure_bind]
    _ = 𝒮[(do
      let pointTable ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      let metadata ← $ᵗ MetadataTable
      pure (pointTable, (nonces, metadata))) >>= next] := by
        rw [evalSPMF_bind, independent_factors, ← evalSPMF_bind]
    _ = _ := by simp only [bind_assoc, pure_bind]

/-- Reverse transport, in the form consumed by the original graph experiment. -/
theorem assemble_bind {α : Type} (next : PrivateTable → Labels → ProbComp α) :
    𝒮[do
      let privateAnswers ← $ᵗ PrivateTable
      let graph ← $ᵗ Labels
      next privateAnswers graph] =
    𝒮[do
      let pointTable ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      let metadata ← $ᵗ MetadataTable
      let factors := (pointTable, (nonces, metadata))
      next (privateTable factors) (labels factors)] := by
  have same := independent_bind (fun factors => next (assemble factors).1 (assemble factors).2)
  have reconstructed (privateAnswers : PrivateTable) (graph : Labels) :
      next (assemble (factor (privateAnswers, graph))).1
        (assemble (factor (privateAnswers, graph))).2 = next privateAnswers graph := by
    rw [assemble_factor]
  simp only [reconstructed] at same
  exact same

/-- Direct factorization of the existing graph experiment, preserving its entire
result (including the original program's recorded costs). -/
theorem graphObserve_factors {α : Type} (program : OracleComp SecurityGameHop.GameWorld α) :
    𝒮[graphObserve program] =
    𝒮[do
      let pointTable ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      let metadata ← $ᵗ MetadataTable
      let factors := (pointTable, (nonces, metadata))
      SecurityGraphHidden.observe (fixPrivate (privateTable factors) program)
        (SecurityGraphSampling.graphCache (privateTable factors)
          SecurityGraphOrder.positions (labels factors) ∅)] := by
  exact assemble_bind (fun privateAnswers graph =>
    SecurityGraphHidden.observe (fixPrivate privateAnswers program)
      (SecurityGraphSampling.graphCache privateAnswers SecurityGraphOrder.positions graph ∅))

end SigGolfCandidate.Hypertree.SecurityGraphFactor
