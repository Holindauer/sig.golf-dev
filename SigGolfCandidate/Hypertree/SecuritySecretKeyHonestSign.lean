import SigGolfCandidate.Hypertree.SecuritySecretKeyHonest

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyHonest
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop SecuritySeparation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem signChain (address : ChainAddress) (message : Digest) :
    Safe allowed (SecurityIdealSign.signChain address message) := by
  unfold SecurityIdealSign.signChain
  simpa only [map_eq_pure_bind] using
    (secret address).bind _ (fun value =>
      (publicCall (walk _ 0 (digit message address.chain).val value
        (chainHash address.level.val address.tree.toNat address.side address.chain))).bind _
        (fun fragment => (publicCall (walk _ (digit message address.chain).val
          (7 - (digit message address.chain).val) fragment
          (chainHash address.level.val address.tree.toNat address.side address.chain))).map
            (fun last => (fragment, last))))

private theorem nodeChoice (level tree : Nat) (side : Bool) (sibling current : Digest) :
    Safe (fun query => ¬SecretKeyEligible query)
      (if side then SecurityReference.node level tree sibling current
        else SecurityReference.node level tree current sibling) := by
  cases side <;> exact node _ _ _ _

theorem signLayerWithRoot (level : Fin 152) (tree : BitVec 192) (side : Bool) (message : Digest) :
    Safe allowed (SecurityIdealSign.signLayerWithRoot level tree side message) := by
  unfold SecurityIdealSign.signLayerWithRoot
  split
  · simpa only [map_eq_pure_bind] using
      (secret ⟨level,tree,side,0⟩).bind _ (fun fragment =>
        (publicCall (chainHash level.val tree.toNat side 0 0 fragment)).bind _ (fun current =>
          (leafRoot level tree (!side)).bind _ (fun sibling =>
            (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
              (fun root => ((⟨fun i => if i = 0 then fragment else 0, sibling⟩ : LayerSignature), root)))))
  · simpa only [map_eq_pure_bind] using
      (sequenceFin 46 _ (fun chain => signChain ⟨level,tree,side,chain⟩ message)).bind _ (fun chains =>
        (publicCall (compressLeaf level.val tree.toNat side (fun i => (chains i).2))).bind _ (fun current =>
          (leafRoot level tree (!side)).bind _ (fun sibling =>
            (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
              (fun root => ((⟨fun i => (chains i).1, sibling⟩ : LayerSignature), root)))))

theorem signUpper (count level index : Nat) (hl : count + level ≤ 152) (hi : index < 2 ^ 192)
    (message : Digest) : Safe allowed (SecurityIdealSign.signUpper count level index hl hi message) := by
  induction count generalizing level index message with
  | zero => exact Safe.pure _
  | succ count ih =>
    simpa only [SecurityIdealSign.signUpper, map_eq_pure_bind] using
      (signLayerWithRoot ⟨level, by omega⟩ (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message).bind _
        (fun layer => (ih (level + 1) (index / 2) (by omega)
          (lt_of_le_of_lt (Nat.div_le_self ..) hi) layer.2).map (fun rest => layer.1 :: rest))

theorem randomizer (message : Message) : Safe allowed (SecurityIdealSign.randomizer message) :=
  Safe.ask (spec := SplitWorld) allowed (.inl (.randomizer message)) trivial

theorem randomizedIndex (pk : PublicKey) (message : Message) :
    Safe allowed (SecurityIdealSign.randomizedIndex pk message) := by
  unfold SecurityIdealSign.randomizedIndex
  simpa only [map_eq_pure_bind] using
    (randomizer message).bind _ (fun nonce =>
      (publicCall (Safe.ask (spec := HashSpec) (fun query => ¬SecretKeyEligible query)
        (SecurityRandomOracle.indexInput pk message nonce)
        (SecurityDomains.not_secretKeyEligible_addressedInput 5 0 0 0 0 0 _ (by decide) (by decide)))).map
        (fun answer => (nonce, answer.extractLsb' 0 152)))

theorem signCompact (pk : PublicKey) (message : Message) : Safe allowed (SecurityIdealSign.signCompact pk message) := by
  unfold SecurityIdealSign.signCompact
  exact (randomizedIndex pk message).bind _ (fun ri =>
    (signLayerWithRoot ⟨0,by decide⟩ _ _ _).bind _ (fun bottom =>
      (signUpper 151 1 (ri.2.toNat / 2) _ _ bottom.2).bind _ (fun _ => Safe.pure _)))

theorem signWire (pk : PublicKey) (message : Message) : Safe allowed (SecurityExperiment.signWire pk message) :=
  (signCompact pk message).map SecurityExperiment.serialize

/-- Honest signing cannot activate the secret key monitor, on any oracle history. -/
theorem stop_signWire_bind {α : Type} (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (next : Option (Bytes submission.sizes.signature) → OracleComp GameWorld α) :
    stop secretKey ((SecurityExperiment.signWire pk message).liftComp GameWorld >>= next) =
      ((SecurityExperiment.signWire pk message).liftComp GameWorld >>= fun response => stop secretKey (next response)) :=
  ((signWire pk message).lift secretKey).stop_bind secretKey next

end SigGolfCandidate.Hypertree.SecuritySecretKeyHonest
