import SigGolfCandidate.Hypertree.SecurityGraphCollision

namespace SigGolfCandidate.Hypertree.SecurityGraphExtraction
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphReference SecurityGraphIdeal
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphCompletion SecurityGraphCollision
  SecurityPath SignatureEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- One actual verification layer collides with its canonical graph target or
supplies an unauthorized canonical WOTS point. All values are from the ideal graph. -/
def LayerBad (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level : Fin 160) (index : Nat) (message : Digest) (signature : LayerSignature) : Prop :=
  LayerCollision (privateTable factors) (labels factors) base level
    (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message signature ∨
  (0 < level.val ∧ ∃ chain, ¬Authorized factors.2.2 signed (pathAddress level index chain, digit message chain) ∧
    signature.values chain = truncate (factors.1 (pathAddress level index chain, digit message chain)))

/-- The bad layer remains attached to the actual verifier's message and index
recurrence. Thus the witness is not an unrelated collision elsewhere in the oracle. -/
def PathBad (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash) :
    Nat → Nat → Digest → List LayerSignature → Prop
  | _, _, _, [] => False
  | level, index, message, signature :: rest =>
      (∃ atLevel : Fin 160, atLevel.val = level ∧ LayerBad factors signed base atLevel index message signature) ∨
      PathBad factors signed base (level + 1) (index / 2)
        (recoverLayer (programmed (privateTable factors) (labels factors) base)
          level (index / 2) (index % 2 == 1) message signature) rest

theorem completed_earlier (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level : Fin 160) (index : Nat) (bound : index < 2 ^ 192) (upper : 0 < level.val)
    (message : Digest) (signature : LayerSignature)
    (exposure : EarlierPointExposure (hash (privateTable factors) (labels factors) base) 0
      level.val index message signature) :
    ∃ chain, ¬Authorized factors.2.2 signed (pathAddress level index chain, digit message chain) ∧
      signature.values chain = truncate (factors.1 (pathAddress level index chain, digit message chain)) := by
  rw [hash_as_derived] at exposure
  have outcome := programmed_earlier_point (residual (privateTable factors) base) 0 (labels factors)
    signed level index bound upper message signature exposure
  simp only [derived_residual] at outcome
  have same : factor (privateTable factors, labels factors) = factors := factor_assemble factors
  rw [same] at outcome
  exact outcome

theorem path_fault (factors : Factors) (signed : Finset (BitVec 160)) (base : Hash)
    (level index : Nat) (message : Digest) (signatures : List LayerSignature)
    (levels : level + signatures.length ≤ 160) (bound : index < 2 ^ 192)
    (fault : PathFault (hash (privateTable factors) (labels factors) base) 0 level index message signatures) :
    PathBad factors signed base level index message signatures := by
  induction signatures generalizing level index message with
  | nil => exact fault
  | cons signature rest ih =>
    rcases fault with first | later
    · left
      have atLevel : level < 160 := by simp only [List.length_cons] at levels; omega
      refine ⟨⟨level, atLevel⟩, rfl, ?_⟩
      rcases first with collision | ⟨positive, earlier⟩
      · left
        have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) bound
        apply layer_collision (privateTable factors) (labels factors) base ⟨level, atLevel⟩
          (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message signature
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt half] using collision
      · right
        exact ⟨positive, completed_earlier factors signed base ⟨level, atLevel⟩ index bound positive message signature earlier⟩
    · right
      rw [recoverLayer_public] at later
      exact ih (level + 1) (index / 2) _ (by simp only [List.length_cons] at levels; omega)
        (lt_of_le_of_lt (Nat.div_le_self ..) bound) later

def publicKey (factors : Factors) : PublicKey := truncate (factors.2.2 (.node 159 0))

noncomputable def index (factors : Factors) (base : Hash) (message : Message) (signature : Compact) : BitVec 160 :=
  indexOf (programmed (privateTable factors) (labels factors) base) (publicKey factors) message signature.randomizer

noncomputable def Signed (factors : Factors) (base : Hash) (history : SecurityForgery.History) : Finset (BitVec 160) :=
  (history.map fun entry => index factors base entry.1 entry.2).toFinset

def HonestHistory (factors : Factors) (base : Hash) (history : SecurityForgery.History) : Prop :=
  ∀ entry ∈ history, entry.2 =
    SecurityGraphSigner.signature (privateTable factors) (labels factors)
      (privateTable factors (.randomizer entry.1))
      (indexOf (programmed (privateTable factors) (labels factors) base) (publicKey factors)
        entry.1 (privateTable factors (.randomizer entry.1)))

def IndexReuse (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (message : Message) (signature : Compact) : Prop :=
  ∃ entry ∈ history,
    SecurityRandomOracle.indexInput (publicKey factors) entry.1 entry.2.randomizer ≠
      SecurityRandomOracle.indexInput (publicKey factors) message signature.randomizer ∧
    index factors base entry.1 entry.2 = index factors base message signature

def BottomExposure (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (message : Message) (signature : Compact) : Prop :=
  ¬Authorized factors.2.2 (Signed factors base history)
    (pathAddress 0 (index factors base message signature).toNat 0, 0) ∧
  signature.bottom = truncate (factors.1 (pathAddress 0 (index factors base message signature).toNat 0, 0))

theorem completed_index (factors : Factors) (base : Hash) (message : Message) (signature : Compact) :
    SecurityForgery.index (hash (privateTable factors) (labels factors) base) 0 message signature =
      index factors base message signature := by
  unfold SecurityForgery.index index
  rw [keygen_label, index_public]
  rfl

theorem completed_signed (factors : Factors) (base : Hash) (history : SecurityForgery.History) :
    signedIndices (hash (privateTable factors) (labels factors) base) 0 history = Signed factors base history := by
  simp only [signedIndices, Signed, completed_index]

/-- Strong-forgery extraction for arbitrary independent private values and graph
labels. Every alternative is secret key-free and tied to the actual accepted verifier path. -/
theorem strong_extraction (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (honest : HonestHistory factors base history) (message : Message) (signature : Compact)
    (accepted : Reference.verify (programmed (privateTable factors) (labels factors) base)
      (publicKey factors) message signature.toReference)
    (fresh : (message, signature) ∉ history) :
    PathBad factors (Signed factors base history) base 0
      (index factors base message signature).toNat 0 signature.toReference.layers ∨
    IndexReuse factors base history message signature ∨ BottomExposure factors base history message signature := by
  have honest' : SecurityForgery.HonestHistory (hash (privateTable factors) (labels factors) base) 0 history := by
    intro entry member
    rw [keygen_label, signCompact_graph]
    exact honest entry member
  have accepted' : Reference.verify (hash (privateTable factors) (labels factors) base)
      (Reference.keygen (hash (privateTable factors) (labels factors) base) 0) message signature.toReference := by
    rw [keygen_label]
    exact (verify_public _ _ _ _ _ _).mpr accepted
  have outcome := SecurityForgery.strong_forgery_extraction
    (hash (privateTable factors) (labels factors) base) 0 history honest' message signature accepted' fresh
  rcases outcome with fault | reuse | bottom
  · left
    unfold SecurityForgery.ForgeryPathFault at fault
    rw [completed_index] at fault
    exact path_fault factors (Signed factors base history) base 0 _ 0 _
      (by rw [accepted.1])
      (lt_of_lt_of_le (index factors base message signature).isLt
        (Nat.pow_le_pow_right (by decide) (by decide))) fault
  · right; left
    have reuse' := SecurityForgery.indexReuse_distinct_inputs _ 0 history message signature reuse
    unfold IndexReuse
    simpa only [keygen_label, completed_index, publicKey, labels_node] using reuse'
  · right; right
    have freshness := fresh_index_not_signed _ 0 history message signature bottom.1
    rw [completed_index, completed_signed] at freshness
    have bound : (index factors base message signature).toNat < 2 ^ 192 :=
      lt_of_lt_of_le (index factors base message signature).isLt
        (Nat.pow_le_pow_right (by decide) (by decide))
    refine ⟨bottom_source_unauthorized _ _ _ freshness, ?_⟩
    have value := bottom.2
    rw [completed_index] at value
    have source := secret_point (privateTable factors) (labels factors) base
      (pathAddress 0 (index factors base message signature).toNat 0)
    have half := lt_of_le_of_lt (Nat.div_le_self (index factors base message signature).toNat 2) bound
    simp only [pathAddress, Fin.val_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt half] at source
    exact value.trans (source.trans (assembled_chainPoint factors _ 0))

theorem index_residual (factors : Factors) (base : Hash) (pk : PublicKey)
    (message : Message) (nonce : Bytes 32) :
    indexOf (programmed (privateTable factors) (labels factors) base) pk message nonce =
      (base (SecurityRandomOracle.indexInput pk message nonce)).extractLsb' 0 160 := by
  change (programmed (privateTable factors) (labels factors) base
    (SecurityRandomOracle.indexInput pk message nonce)).extractLsb' 0 160 = _
  rw [SecurityGraphSigner.programmed_index]

/-- The same extraction with hypotheses directly on the actual ideal signer and
monadic verifier outputs, rather than an assumed graph-signature interface. -/
theorem ideal_strong_extraction (factors : Factors) (base : Hash) (history : SecurityForgery.History)
    (honest : ∀ entry ∈ history, entry.2 = evalWithAnswerFn
      (SecurityGraphSigner.answers (privateTable factors)
        (programmed (privateTable factors) (labels factors) base))
      (SecurityIdealSign.signCompact (publicKey factors) entry.1))
    (message : Message) (signature : Compact)
    (accepted : evalWithAnswerFn (programmed (privateTable factors) (labels factors) base)
      (SecurityVerify.verifyCompact (publicKey factors) message signature) = true)
    (fresh : (message, signature) ∉ history) :
    PathBad factors (Signed factors base history) base 0
      (index factors base message signature).toNat 0 signature.toReference.layers ∨
    IndexReuse factors base history message signature ∨ BottomExposure factors base history message signature := by
  apply strong_extraction factors base history _ message signature
    ((SecurityVerify.eval_verifyCompact_iff _ _ _ _).mp accepted) fresh
  intro entry member
  have response := honest entry member
  rw [SecurityGraphSigner.eval_signCompact] at response
  simpa only [index_residual] using response

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphExtraction.strong_extraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms strong_extraction
/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphExtraction.ideal_strong_extraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ideal_strong_extraction
end SigGolfCandidate.Hypertree.SecurityGraphExtraction
