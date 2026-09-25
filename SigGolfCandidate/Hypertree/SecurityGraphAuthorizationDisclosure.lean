import SigGolfCandidate.Hypertree.SecurityGraphAuthorizationReference

namespace SigGolfCandidate.Hypertree.SecurityGraphAuthorization
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphFrontier SecurityGraphPassive
  SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Public bottom-chain outputs require no signing response to be disclosed. -/
theorem bottom_positive_authorized (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (address : ChainAddress) (point : Fin 8) (bottom : address.level.val = 0)
    (positive : 0 < point.val) : Authorized metadata signed (address, point) := by
  simp only [Authorized, bottom, if_true]
  exact Or.inl positive

/-- Every upper layer of an honest signature reveals only its globally authorized
canonical digit. Subsequent layers' messages are the appropriate public node labels. -/
theorem upperPoints_authorized (factors : Factors) (signed : Finset (BitVec 160))
    (count level index : Nat) (levels : count + level ≤ 160) (bound : index < 2 ^ 192)
    (positive : 0 < level) (message : Digest)
    (canonical : message = truncate (factors.2.2
      (.node ⟨level - 1, by omega⟩ (BitVec.ofNat 192 index)))) :
    ∀ point ∈ upperPoints (labels factors) count level index levels bound message,
      Authorized factors.2.2 signed point := by
  induction count generalizing level index message with
  | zero => simp [upperPoints]
  | succ count ih =>
    intro point member
    change point ∈ layerPoints ⟨level, by omega⟩ (BitVec.ofNat 192 (index / 2))
      (index % 2 == 1) message ∪ _ at member
    rcases Finset.mem_union.mp member with first | rest
    · simp only [layerPoints, show level ≠ 0 by omega, if_false, Finset.mem_image,
        Finset.mem_univ, true_and] at first
      obtain ⟨chain, rfl⟩ := first
      change Authorized factors.2.2 signed
        (pathAddress ⟨level, by omega⟩ index chain, digit message chain)
      simp only [Authorized, pathAddress, show level ≠ 0 by omega, if_false]
      change (threshold factors.2.2 (pathAddress ⟨level, by omega⟩ index chain)).val ≤ _
      rw [threshold_pathAddress _ _ _ _ bound, canonical]
    · apply ih (level + 1) (index / 2) (by omega)
        (lt_of_le_of_lt (Nat.div_le_self ..) bound) (by omega)
        (truncate (labels factors (.node ⟨level, by omega⟩ (BitVec.ofNat 192 (index / 2)))))
        _ point rest
      simp only [labels_node, Nat.add_sub_cancel]

/-- Whole-signature disclosure is covered by the conservative frontier after
inserting its actual index. This includes all 159 upper WOTS digit vectors. -/
theorem signaturePoints_authorized (factors : Factors) (signed : Finset (BitVec 160))
    (index : BitVec 160) (member : index ∈ signed) :
    ∀ point ∈ signaturePoints (labels factors) index, Authorized factors.2.2 signed point := by
  have bound : index.toNat < 2 ^ 192 := lt_of_lt_of_le index.isLt
    (Nat.pow_le_pow_right (by decide) (by decide))
  intro point located
  rcases Finset.mem_union.mp located with first | rest
  · simp only [layerPoints, Fin.val_zero, if_true, Finset.mem_singleton] at first
    subst point
    change Authorized factors.2.2 signed (pathAddress 0 index.toNat 0, 0)
    simp only [Authorized, pathAddress, Fin.val_zero, if_true, Nat.lt_irrefl, false_or]
    exact ⟨index, member, childIndex_pathAddress 0 index.toNat 0 bound⟩
  · exact upperPoints_authorized factors signed 159 1 (index.toNat / 2) (by decide)
      (lt_of_le_of_lt (Nat.div_le_self ..) bound) (by decide) _ rfl point rest

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphAuthorization.signaturePoints_authorized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signaturePoints_authorized
end SigGolfCandidate.Hypertree.SecurityGraphAuthorization
