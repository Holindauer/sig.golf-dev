import SigGolfCandidate.Hypertree.SecurityGraphAuthorization

namespace SigGolfCandidate.Hypertree.SecurityGraphAuthorization
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphFrontier SecurityGraphPassive
  SecurityGraphFactor SecurityGraphReference
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The graph factorization of the canonical chain walk used in extraction. -/
theorem programmed_path_walk (residual : Hash) (secretKey : SecretKey) (graph : Labels)
    (level : Fin 160) (index : Nat) (chain : Chain) (point : Fin 8)
    (bound : index < 2 ^ 192) :
    walk (chainHash (programmed (derived residual secretKey) graph residual)
      level.val (index / 2) (index % 2 == 1) chain) 0 point.val
      (secret (programmed (derived residual secretKey) graph residual) secretKey level.val
        (index / 2) (index % 2 == 1) chain) =
      truncate ((factor (derived residual secretKey, graph)).1 (pathAddress level index chain, point)) := by
  have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
  have step := programmed_walk residual secretKey graph (pathAddress level index chain) point.val
    (by have := point.isLt; omega)
  rw [chainPoint_eq] at step
  simpa only [pathAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt half, factor] using step

theorem programmed_canonical_child (residual : Hash) (secretKey : SecretKey) (graph : Labels)
    (level : Fin 160) (index : Nat) (bound : index < 2 ^ 192) :
    SecurityPath.canonicalChild (programmed (derived residual secretKey) graph residual) secretKey
      level.val index =
      truncate ((factor (derived residual secretKey, graph)).2.2
        (.node ⟨level.val - 1, by omega⟩ (BitVec.ofNat 192 index))) := by
  have root := programmed_treeRoot residual secretKey graph
    ⟨level.val - 1, by omega⟩ (BitVec.ofNat 192 index)
  simpa only [SecurityPath.canonicalChild, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    factor_node] using root

/-- Concrete canonical-graph instantiation of the extracted earlier-point event.
The output is an actual forged fragment equal to an unauthorized sampled point. -/
theorem programmed_earlier_point (residual : Hash) (secretKey : SecretKey) (graph : Labels)
    (signed : Finset (BitVec 160)) (level : Fin 160) (index : Nat)
    (bound : index < 2 ^ 192) (upper : 0 < level.val)
    (message : Digest) (signature : LayerSignature)
    (exposure : SecurityPath.EarlierPointExposure
      (programmed (derived residual secretKey) graph residual) secretKey level.val index message signature) :
    ∃ chain,
      ¬Authorized (factor (derived residual secretKey, graph)).2.2 signed
        (pathAddress level index chain, digit message chain) ∧
      signature.values chain = truncate ((factor (derived residual secretKey, graph)).1
        (pathAddress level index chain, digit message chain)) := by
  apply earlier_point_unauthorized _ secretKey _ signed level index bound upper message signature
    (programmed_canonical_child residual secretKey graph level index bound) _ exposure
  intro chain same
  exact same.trans (programmed_path_walk residual secretKey graph level index chain (digit message chain) bound)

/-- Only indices occurring in actual signing responses open bottom sources. -/
def signedIndices (hash : Hash) (secretKey : SecretKey) (history : SecurityForgery.History) :
    Finset (BitVec 160) :=
  (history.map fun entry => SecurityForgery.index hash secretKey entry.1 entry.2).toFinset

theorem fresh_index_not_signed (hash : Hash) (secretKey : SecretKey) (history : SecurityForgery.History)
    (message : Message) (signature : SignatureEncoding.Compact)
    (fresh : ∀ entry ∈ history, SecurityForgery.index hash secretKey entry.1 entry.2 ≠
      SecurityForgery.index hash secretKey message signature) :
    SecurityForgery.index hash secretKey message signature ∉ signedIndices hash secretKey history := by
  simp only [signedIndices, List.mem_toFinset, List.mem_map]
  rintro ⟨entry, member, same⟩
  exact fresh entry member same

/-- The bottom alternative of strong-forgery extraction produces the unopened
source point at exactly the forged message's actual 160-bit index. -/
theorem programmed_new_bottom (residual : Hash) (secretKey : SecretKey) (graph : Labels)
    (history : SecurityForgery.History) (message : Message) (signature : SignatureEncoding.Compact)
    (exposure : SecurityForgery.NewBottomExposure
      (programmed (derived residual secretKey) graph residual) secretKey history message signature) :
    let hash := programmed (derived residual secretKey) graph residual
    let index := SecurityForgery.index hash secretKey message signature
    ¬Authorized (factor (derived residual secretKey, graph)).2.2 (signedIndices hash secretKey history)
      (pathAddress 0 index.toNat 0, 0) ∧
    signature.bottom = truncate ((factor (derived residual secretKey, graph)).1
      (pathAddress 0 index.toNat 0, 0)) := by
  dsimp only
  let hash := programmed (derived residual secretKey) graph residual
  let index := SecurityForgery.index hash secretKey message signature
  have bound : index.toNat < 2 ^ 192 := lt_of_lt_of_le index.isLt
    (Nat.pow_le_pow_right (by decide) (by decide))
  refine ⟨bottom_source_unauthorized _ _ _
    (fresh_index_not_signed hash secretKey history message signature exposure.1), ?_⟩
  exact exposure.2.trans (programmed_path_walk residual secretKey graph 0 index.toNat 0 0 bound)

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphAuthorization.programmed_earlier_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms programmed_earlier_point
/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphAuthorization.programmed_new_bottom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms programmed_new_bottom
end SigGolfCandidate.Hypertree.SecurityGraphAuthorization
