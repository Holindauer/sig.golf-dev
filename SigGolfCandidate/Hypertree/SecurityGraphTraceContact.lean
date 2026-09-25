import SigGolfCandidate.Hypertree.SecurityVerifyTrace
import SigGolfCandidate.Hypertree.SecurityGraphChainMonitor

namespace SigGolfCandidate.Hypertree.SecurityGraphTraceContact
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphReference
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphCollision SecurityGraphQuery
  SecurityGraphContact SecurityGraphChainMonitor SecurityExtraction SecurityRandomOracle SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A concrete public call returns its address's canonical target from a distinct input. -/
def CollisionContact (factors : Factors) (hash : Hash) (query : Query) : Prop :=
  ∃ position, locate query = some position ∧
    query ≠ position.input (privateTable factors) (labels factors) ∧
    truncate (hash query) = truncate (labels factors position)

/-- A concrete chain call guesses an unauthorized canonical predecessor. -/
def HiddenContact (factors : Factors) (signed : Finset (BitVec 160)) (query : Query) : Prop :=
  ∃ address step, ¬Authorized factors.2.2 signed (predecessor address step) ∧
    query = chainInput address step (truncate (factors.1 (predecessor address step)))

def Contact (factors : Factors) (signed : Finset (BitVec 160)) (hash : Hash) (query : Query) : Prop :=
  CollisionContact factors hash query ∨ HiddenContact factors signed query

theorem payload_collision (factors : Factors) (base : Hash) (position : Position)
    (expected actual : List Byte)
    (canonical : position.address.input expected = position.input (privateTable factors) (labels factors))
    (collision : CollisionAt (programmed (privateTable factors) (labels factors) base)
      position.address.tag.val position.address.level.val position.address.tree.toNat position.address.leaf.val
      position.address.chain.val position.address.step.val expected actual) :
    CollisionContact factors (programmed (privateTable factors) (labels factors) base)
      (position.address.input actual) := by
  refine ⟨position, locate_address position actual, ?_, ?_⟩
  · rw [←canonical]
    exact collision.1
  · have target := collision.2
    change truncate (programmed (privateTable factors) (labels factors) base (position.address.input actual)) =
      truncate (programmed (privateTable factors) (labels factors) base (position.address.input expected)) at target
    rw [canonical, programmed_graph] at target
    exact target

theorem canonical_chain_input (factors : Factors) (address : ChainAddress) (step : Fin 7) :
    chainInput address step (chainPoint (privateTable factors) (labels factors) address ⟨step.val, by omega⟩) =
      (Position.chain address step).input (privateTable factors) (labels factors) := rfl

/-- Every collision alternative carries an input in the actual layer query log
and the target equality recognized by the public monitor. -/
theorem layer_collision_logged (factors : Factors) (base : Hash) (level : Fin 160)
    (tree : BitVec 192) (side : Bool) (message : Digest) (signature : LayerSignature)
    (collision : LayerCollision (privateTable factors) (labels factors) base level tree side message signature) :
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.recoverLayer level.val tree.toNat side message signature),
      CollisionContact factors (programmed (privateTable factors) (labels factors) base) query := by
  rcases collision with nodeHit | other
  · refine ⟨_, mem_recoverLayer_node _ _ _ _ _ _, ?_⟩
    exact payload_collision factors base (.node level tree) _ _ rfl nodeHit
  · by_cases bottom : level.val = 0
    · rw [if_pos bottom] at other
      have adapted : CollisionAt (programmed (privateTable factors) (labels factors) base)
          2 level.val tree.toNat (sideNumber side) 0 0
          (bytes (chainPoint (privateTable factors) (labels factors) ⟨level, tree, side, 0⟩ 0))
          (bytes (signature.values 0)) := by
        rw [bottom]
        exact other
      have contact := payload_collision factors base (.chain ⟨level, tree, side, 0⟩ 0)
        (bytes (chainPoint (privateTable factors) (labels factors) ⟨level, tree, side, 0⟩ 0))
        (bytes (signature.values 0)) (canonical_chain_input factors ⟨level, tree, side, 0⟩ 0) adapted
      refine ⟨_, mem_recoverLayer_leaf _ _ _ _ _ _ _ ?_, contact⟩
      change addressedInput 2 level.val tree.toNat (sideNumber side) 0 0 (bytes (signature.values 0)) ∈ _
      rw [bottom]
      exact mem_recoverLeaf_bottom
        (programmed (privateTable factors) (labels factors) base) tree.toNat side message signature
    · rw [if_neg bottom] at other
      rcases other with leafHit | ⟨chain, offset, within, chainHit⟩
      · refine ⟨_, mem_recoverLayer_leaf _ _ _ _ _ _ _
          (mem_recoverLeaf_compress _ _ _ _ _ _ bottom), ?_⟩
        exact payload_collision factors base (.leaf level tree side) _ _ rfl leafHit
      · let step : Fin 7 := ⟨(digit message chain).val + offset,
          by have := (digit message chain).isLt; omega⟩
        refine ⟨_, mem_recoverLayer_leaf _ _ _ _ _ _ _
          (mem_recoverLeaf_chain _ _ _ _ _ _ bottom chain offset within), ?_⟩
        exact payload_collision factors base (.chain ⟨level, tree, side, chain⟩ step) _ _
          (canonical_chain_input factors ⟨level, tree, side, chain⟩ step) chainHit

/-- Unauthorized points cannot be endpoints, which ensures their successor call
is executed by a verifying WOTS suffix. -/
theorem unauthorized_lt_seven (factors : Factors) (signed : Finset (BitVec 160))
    (address : ChainAddress) (point : Fin 8) (hidden : ¬Authorized factors.2.2 signed (address, point)) :
    point.val < 7 := by
  have limit := point.isLt
  by_contra large
  have equal : point = 7 := Fin.ext (by change point.val = 7; omega)
  exact hidden (equal ▸ endpoint_authorized factors.2.2 signed address)

theorem upper_point_logged (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level : Fin 160) (index : Nat) (bound : index < 2 ^ 192) (upper : 0 < level.val)
    (message : Digest) (signature : LayerSignature) (chain : Chain)
    (hidden : ¬Authorized factors.2.2 signed (pathAddress level index chain, digit message chain))
    (value : signature.values chain = truncate (factors.1 (pathAddress level index chain, digit message chain))) :
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.recoverLayer level.val (index / 2) (index % 2 == 1) message signature),
      HiddenContact factors signed query := by
  have short := unauthorized_lt_seven factors signed _ _ hidden
  have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
  let address := pathAddress level index chain
  let step : Fin 7 := ⟨(digit message chain).val, short⟩
  have member := mem_recoverLayer_leaf (programmed (privateTable factors) (labels factors) base)
    level.val (index / 2) (index % 2 == 1) message signature _
    (mem_recoverLeaf_chain _ _ _ _ _ _ (by omega) chain 0 (by omega))
  simp only [Nat.add_zero, Hypertree.walk] at member
  refine ⟨_, member, address, step, hidden, ?_⟩
  change addressedInput 2 level.val (index / 2) (sideNumber (index % 2 == 1)) chain.val
    (digit message chain).val (bytes (signature.values chain)) =
    addressedInput 2 level.val (BitVec.ofNat 192 (index / 2)).toNat (sideNumber (index % 2 == 1)) chain.val
      (digit message chain).val (bytes (truncate (factors.1 (pathAddress level index chain, digit message chain))))
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt half, value]

end SigGolfCandidate.Hypertree.SecurityGraphTraceContact
