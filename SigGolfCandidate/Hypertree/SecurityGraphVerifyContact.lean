import SigGolfCandidate.Hypertree.SecurityGraphTraceContact

namespace SigGolfCandidate.Hypertree.SecurityGraphVerifyContact
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityDerivation SecurityGraph SecurityGraphReference
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphCollision SecurityGraphQuery
  SecurityGraphContact SecurityGraphChainMonitor SecurityGraphExtraction SecurityGraphTraceContact
  SecurityRandomOracle SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem mem_layers_head (hash : Hash) (level index : Nat) (message : Digest)
    (signature : LayerSignature) (rest : List LayerSignature) (query : Query)
    (member : query ∈ queries hash (SecurityVerify.recoverLayer level (index / 2) (index % 2 == 1) message signature)) :
    query ∈ queries hash (SecurityVerify.recoverLayers level index message (signature :: rest)) := by
  rw [SecurityVerify.recoverLayers, queries_bind]
  exact List.mem_append_left _ member

theorem mem_layers_tail (hash : Hash) (level index : Nat) (message : Digest)
    (signature : LayerSignature) (rest : List LayerSignature) (query : Query)
    (member : query ∈ queries hash (SecurityVerify.recoverLayers (level + 1) (index / 2)
      (recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest)) :
    query ∈ queries hash (SecurityVerify.recoverLayers level index message (signature :: rest)) := by
  rw [SecurityVerify.recoverLayers, queries_bind, SecurityVerify.eval_recoverLayer]
  exact List.mem_append_right _ member

theorem mem_verify_layers (hash : Hash) (pk : PublicKey) (message : Message) (signature : Compact) (query : Query)
    (member : query ∈ queries hash (SecurityVerify.recoverLayers 0
      (indexOf hash pk message signature.randomizer).toNat 0 signature.toReference.layers)) :
    query ∈ queries hash (SecurityVerify.verifyCompact pk message signature) := by
  simp only [SecurityVerify.verifyCompact, queries_bind, queries_pure, List.append_nil, SecurityReference.eval_ask]
  exact List.mem_append_right _ member

theorem mem_verify_index (hash : Hash) (pk : PublicKey) (message : Message) (signature : Compact) :
    indexInput pk message signature.randomizer ∈ queries hash (SecurityVerify.verifyCompact pk message signature) := by
  rw [SecurityVerify.verifyCompact, queries_bind]
  exact List.mem_append_left _ (by simp [indexInput])

theorem layer_bad_logged (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level : Fin 160) (index : Nat) (bound : index < 2 ^ 192) (message : Digest) (signature : LayerSignature)
    (bad : LayerBad factors signed base level index message signature) :
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.recoverLayer level.val (index / 2) (index % 2 == 1) message signature),
      Contact factors signed (programmed (privateTable factors) (labels factors) base) query := by
  rcases bad with collision | ⟨positive, chain, hidden, value⟩
  · obtain ⟨query, member, contact⟩ := layer_collision_logged factors base level
      (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message signature collision
    have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt half] at member
    exact ⟨query, member, Or.inl contact⟩
  · obtain ⟨query, member, contact⟩ := upper_point_logged factors signed base level index bound positive
      message signature chain hidden value
    exact ⟨query, member, Or.inr contact⟩

/-- A bad path necessarily contains a concrete logged public call, even when its
location and all intermediate verifier messages depend on earlier hash answers. -/
theorem path_bad_logged (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level index : Nat) (message : Digest) (signatures : List LayerSignature) (bound : index < 2 ^ 192)
    (bad : PathBad factors signed base level index message signatures) :
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.recoverLayers level index message signatures),
      Contact factors signed (programmed (privateTable factors) (labels factors) base) query := by
  induction signatures generalizing level index message with
  | nil => exact False.elim bad
  | cons signature rest ih =>
    rcases bad with ⟨atLevel, same, first⟩ | later
    · obtain ⟨query, member, contact⟩ := layer_bad_logged factors signed base atLevel index bound message signature first
      rw [same] at member
      exact ⟨query, mem_layers_head _ _ _ _ _ _ _ member, contact⟩
    · obtain ⟨query, member, contact⟩ := ih (level + 1) (index / 2) _
        (lt_of_le_of_lt (Nat.div_le_self ..) bound) later
      exact ⟨query, mem_layers_tail _ _ _ _ _ _ _ member, contact⟩

/-- The fresh bottom source is itself the payload of the verifier's first chain
call, hence is observed even if the rest of the submitted witness is malformed. -/
theorem bottom_logged (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (message : Message) (signature : Compact) (bottom : BottomExposure factors base history message signature) :
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.verifyCompact (publicKey factors) message signature),
      HiddenContact factors (Signed factors base history) query := by
  let atIndex := index factors base message signature
  let address := pathAddress 0 atIndex.toNat 0
  let query := addressedInput 2 0 (atIndex.toNat / 2) (sideNumber (atIndex.toNat % 2 == 1)) 0 0 (bytes signature.bottom)
  have bound : atIndex.toNat < 2 ^ 192 := lt_of_lt_of_le atIndex.isLt
    (Nat.pow_le_pow_right (by decide) (by decide))
  have half : atIndex.toNat / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
  refine ⟨query, mem_verify_layers _ _ _ _ _ ?_, address, 0, bottom.1, ?_⟩
  · change query ∈ queries _ (SecurityVerify.recoverLayers 0 atIndex.toNat 0
      (⟨fun chain => if chain = 0 then signature.bottom else 0, signature.sibling⟩ :: signature.upper))
    apply mem_layers_head
    apply mem_recoverLayer_leaf
    exact mem_recoverLeaf_bottom _ (atIndex.toNat / 2) (atIndex.toNat % 2 == 1) 0
      ⟨fun chain => if chain = 0 then signature.bottom else 0, signature.sibling⟩
  · change addressedInput 2 0 (atIndex.toNat / 2) (sideNumber (atIndex.toNat % 2 == 1)) 0 0
      (bytes signature.bottom) = addressedInput 2 0 (BitVec.ofNat 192 (atIndex.toNat / 2)).toNat
        (sideNumber (atIndex.toNat % 2 == 1)) 0 0
        (bytes (truncate (factors.1 (pathAddress 0 atIndex.toNat 0, 0))))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt half, bottom.2]

/-- An actual accepted fresh ideal signature produces either index reuse or a
specific verifier query satisfying exactly the public monitor's contact predicates. -/
theorem ideal_forgery_logged (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (honest : ∀ entry ∈ history, entry.2 = evalWithAnswerFn
      (SecurityGraphSigner.answers (privateTable factors)
        (programmed (privateTable factors) (labels factors) base))
      (SecurityIdealSign.signCompact (publicKey factors) entry.1))
    (message : Message) (signature : Compact)
    (accepted : evalWithAnswerFn (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.verifyCompact (publicKey factors) message signature) = true)
    (fresh : (message, signature) ∉ history) :
    IndexReuse factors base history message signature ∨
    ∃ query ∈ queries (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.verifyCompact (publicKey factors) message signature),
      Contact factors (Signed factors base history) (programmed (privateTable factors) (labels factors) base) query := by
  rcases ideal_strong_extraction factors base history honest message signature accepted fresh with path | reuse | bottom
  · right
    obtain ⟨query, member, contact⟩ := path_bad_logged factors (Signed factors base history) base 0 _ 0 _
      (lt_of_lt_of_le (index factors base message signature).isLt
        (Nat.pow_le_pow_right (by decide) (by decide))) path
    exact ⟨query, mem_verify_layers _ _ _ _ _ member, contact⟩
  · exact Or.inl reuse
  · right
    obtain ⟨query, member, contact⟩ := bottom_logged factors base history message signature bottom
    exact ⟨query, member, Or.inr contact⟩

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphVerifyContact.ideal_forgery_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ideal_forgery_logged
end SigGolfCandidate.Hypertree.SecurityGraphVerifyContact
