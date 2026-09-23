import SigGolfCandidate.Hypertree.SecurityGraphFactor
import SigGolfCandidate.Hypertree.SecurityForgery

namespace SigGolfCandidate.Hypertree.SecurityGraphAuthorization
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphFrontier SecurityGraphPassive
  SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The child index represented by a tree address and its selected side. -/
def childIndex (address : ChainAddress) : Nat :=
  2 * address.tree.toNat + sideNumber address.side

/-- The upper signing digit depends only on independent public node metadata. -/
def threshold (metadata : MetadataTable) (address : ChainAddress) : Fin 8 :=
  digit (truncate (metadata (.node ⟨address.level.val - 1, by omega⟩
    (BitVec.ofNat 192 (childIndex address))))) address.chain

/-- A conservative public frontier: every upper canonical suffix is available
from setup; bottom sources become available only for actually signed indices. -/
def Authorized (metadata : MetadataTable) (signed : Finset (BitVec 160)) (point : Point) : Prop :=
  if point.1.level.val = 0 then
    0 < point.2.val ∨ ∃ index ∈ signed, childIndex point.1 = index.toNat
  else (threshold metadata point.1).val ≤ point.2.val

theorem authorized_mono (metadata : MetadataTable) {first second : Finset (BitVec 160)}
    (subset : first ⊆ second) {point : Point} (known : Authorized metadata first point) :
    Authorized metadata second point := by
  by_cases bottom : point.1.level.val = 0
  · simp only [Authorized, bottom, if_true] at *
    rcases known with positive | ⟨index, member, same⟩
    · exact Or.inl positive
    · exact Or.inr ⟨index, subset member, same⟩
  · simpa only [Authorized, bottom, if_false] using known

theorem endpoint_authorized (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (address : ChainAddress) : Authorized metadata signed (address, 7) := by
  unfold Authorized
  split
  · exact Or.inl (by change 0 < 7; omega)
  · exact Nat.le_of_lt_succ (threshold metadata address).isLt

theorem below_threshold_unauthorized (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (address : ChainAddress) (point : Fin 8) (upper : 0 < address.level.val)
    (earlier : point.val < (threshold metadata address).val) :
    ¬Authorized metadata signed (address, point) := by
  simp only [Authorized, show address.level.val ≠ 0 by omega, if_false]
  exact Nat.not_le.mpr earlier

theorem div_side (index : Nat) : 2 * (index / 2) + sideNumber (index % 2 == 1) = index := by
  have remainder := Nat.mod_lt index (by decide : 0 < 2)
  have decomposition := Nat.mod_add_div index 2
  by_cases side : index % 2 = 1 <;> simp [sideNumber, side] <;> omega

/-- No address wrapping occurs anywhere on a 160-layer authentication path. -/
def pathAddress (level : Fin 160) (index : Nat) (chain : Chain) : ChainAddress :=
  ⟨level, BitVec.ofNat 192 (index / 2), index % 2 == 1, chain⟩

theorem childIndex_pathAddress (level : Fin 160) (index : Nat) (chain : Chain)
    (bound : index < 2 ^ 192) : childIndex (pathAddress level index chain) = index := by
  have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
  simpa only [childIndex, pathAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt half] using div_side index

theorem threshold_pathAddress (metadata : MetadataTable) (level : Fin 160)
    (index : Nat) (chain : Chain) (bound : index < 2 ^ 192) :
    threshold metadata (pathAddress level index chain) =
      digit (truncate (metadata (.node ⟨level.val - 1, by omega⟩ (BitVec.ofNat 192 index)))) chain := by
  unfold threshold
  rw [childIndex_pathAddress level index chain bound]
  rfl

theorem bottom_source_unauthorized (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (index : BitVec 160) (fresh : index ∉ signed) :
    ¬Authorized metadata signed (pathAddress 0 index.toNat 0, 0) := by
  have bound : index.toNat < 2 ^ 192 := lt_of_lt_of_le index.isLt
    (Nat.pow_le_pow_right (by decide) (by decide))
  simp only [Authorized, pathAddress, Fin.val_zero, ↓reduceIte, Nat.lt_irrefl, false_or]
  intro ⟨other, member, same⟩
  have actual := childIndex_pathAddress 0 index.toNat 0 bound
  change childIndex (pathAddress 0 index.toNat 0) = other.toNat at same
  have equal : index = other := BitVec.eq_of_toNat_eq (actual.symm.trans same)
  exact fresh (equal ▸ member)

/-- Reference extraction identifies a genuinely unopened graph coordinate once
its canonical child and chain point have been related to the sampled graph. -/
theorem earlier_point_unauthorized (hash : Hash) (secretKey : SecretKey) (factors : Factors)
    (signed : Finset (BitVec 160)) (level : Fin 160) (index : Nat)
    (bound : index < 2 ^ 192) (upper : 0 < level.val)
    (message : Digest) (signature : LayerSignature)
    (child : SecurityPath.canonicalChild hash secretKey level.val index =
      truncate (factors.2.2 (.node ⟨level.val - 1, by omega⟩ (BitVec.ofNat 192 index))))
    (points : ∀ chain, signature.values chain =
      walk (chainHash hash level.val (index / 2) (index % 2 == 1) chain) 0
        (digit message chain).val (secret hash secretKey level.val (index / 2) (index % 2 == 1) chain) →
      signature.values chain = truncate (factors.1 (pathAddress level index chain, digit message chain)))
    (exposure : SecurityPath.EarlierPointExposure hash secretKey level.val index message signature) :
    ∃ chain, ¬Authorized factors.2.2 signed (pathAddress level index chain, digit message chain) ∧
      signature.values chain = truncate (factors.1 (pathAddress level index chain, digit message chain)) := by
  obtain ⟨chain, earlier, same⟩ := exposure
  refine ⟨chain, below_threshold_unauthorized _ _ _ _ upper ?_, points chain same⟩
  rw [threshold_pathAddress _ _ _ _ bound]
  simpa only [child] using earlier

end SigGolfCandidate.Hypertree.SecurityGraphAuthorization
