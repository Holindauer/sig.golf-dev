import SigGolfCandidate.Hypertree.SecurityAtomicCounts
import SigGolfCandidate.Hypertree.SecurityExperiment

namespace SigGolfCandidate.Hypertree.SecurityAtomicCounts
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop SecurityAtomicCutoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The digit split changes intermediate values but never the total seven-step
chain work, on every independent answer history. -/
theorem signChain (address : ChainAddress) (message : Digest) :
    Queries (SecurityIdealSign.signChain address message) 8 := by
  have all : Queries (SecurityIdealSign.signChain address message)
      (1 + ((digit message address.chain).val + (7 - (digit message address.chain).val))) := by
    unfold SecurityIdealSign.signChain
    simpa only [map_eq_pure_bind] using
      (secret address).bind _ (fun value =>
        (publicCall (walk _ 0 (digit message address.chain).val value
          (chainHash address.level.val address.tree.toNat address.side address.chain))).bind _
          (fun fragment => (publicCall (walk _ (digit message address.chain).val
            (7 - (digit message address.chain).val) fragment
            (chainHash address.level.val address.tree.toNat address.side address.chain))).map
              (fun last => (fragment, last))))
  have digitBound := (digit message address.chain).isLt
  have total : 1 + ((digit message address.chain).val + (7 - (digit message address.chain).val)) = 8 := by omega
  rw [total] at all
  exact all

private theorem nodeChoice (level tree : Nat) (side : Bool) (sibling current : Digest) :
    Queries (if side then SecurityReference.node level tree sibling current
      else SecurityReference.node level tree current sibling) 1 := by
  cases side <;> exact node _ _ _ _

theorem signLayerWithRoot (level : Fin 152) (tree : BitVec 192) (side : Bool) (message : Digest) :
    Queries (SecurityIdealSign.signLayerWithRoot level tree side message)
      (if level.val = 0 then 5 else 739) := by
  by_cases bottom : level.val = 0
  · have sibling : Queries (SecurityIdealKeygen.leafRoot level tree (!side)) 2 := by
      simpa only [if_pos bottom] using leafRoot level tree (!side)
    simp only [SecurityIdealSign.signLayerWithRoot, if_pos bottom]
    simpa only [map_eq_pure_bind] using
      (secret ⟨level, tree, side, 0⟩).bind _ (fun fragment =>
        (publicCall (chainHash level.val tree.toNat side 0 0 fragment)).bind _ (fun current =>
          sibling.bind _ (fun sibling => (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
            (fun root => ((⟨fun i => if i = 0 then fragment else 0, sibling⟩ : LayerSignature), root)))))
  · have sibling : Queries (SecurityIdealKeygen.leafRoot level tree (!side)) 369 := by
      simpa only [if_neg bottom] using leafRoot level tree (!side)
    simp only [SecurityIdealSign.signLayerWithRoot, if_neg bottom]
    simpa only [map_eq_pure_bind] using
      (sequenceFin 46 8 _ (fun chain => signChain ⟨level, tree, side, chain⟩ message)).bind _ (fun chains =>
        (publicCall (compressLeaf level.val tree.toNat side (fun i => (chains i).2))).bind _ (fun current =>
          sibling.bind _ (fun sibling => (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
            (fun root => ((⟨fun i => (chains i).1, sibling⟩ : LayerSignature), root)))))

theorem signUpper (count level index : Nat) (hl : count + level ≤ 152) (hi : index < 2 ^ 192)
    (message : Digest) (positive : 0 < level) :
    Queries (SecurityIdealSign.signUpper count level index hl hi message) (739 * count) := by
  induction count generalizing level index message with
  | zero => exact Queries.pure _
  | succ count ih =>
    have first : Queries (SecurityIdealSign.signLayerWithRoot ⟨level, by omega⟩
        (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message) 739 := by
      simpa only [if_neg (by omega : level ≠ 0)] using
        signLayerWithRoot ⟨level, by omega⟩ (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message
    simpa only [SecurityIdealSign.signUpper, Nat.mul_succ, Nat.add_comm, map_eq_pure_bind] using
      first.bind _ (fun layer =>
        (ih (level + 1) (index / 2) (by omega) (lt_of_le_of_lt (Nat.div_le_self ..) hi) layer.2 (by omega)).map
          (fun rest => layer.1 :: rest))

theorem randomizer (message : Message) : Queries (SecurityIdealSign.randomizer message) 1 := by
  change Queries (liftM (SplitWorld.query (.inl (.randomizer message)))) 1
  exact Queries.ask (spec := SplitWorld) _

theorem randomizedIndex (pk : PublicKey) (message : Message) :
    Queries (SecurityIdealSign.randomizedIndex pk message) 2 := by
  unfold SecurityIdealSign.randomizedIndex
  simpa only [map_eq_pure_bind] using
    (randomizer message).bind _ (fun nonce =>
      (publicCall (Queries.ask (spec := HashSpec) (SecurityRandomOracle.indexInput pk message nonce))).map
        (fun answer => (nonce, answer.extractLsb' 0 152)))

/-- Full ideal signer query shape is constant for every possible oracle history,
not only answers induced by a consistent function or secretKeyed oracle. -/
theorem signCompact_queries (pk : PublicKey) (message : Message) :
    Queries (SecurityIdealSign.signCompact pk message) 111596 := by
  unfold SecurityIdealSign.signCompact
  refine Queries.bind (nextCost := 111594) (randomizedIndex pk message) _ ?_
  intro ri
  refine Queries.bind (cost := 5) (nextCost := 111589) ?_ _ ?_
  · exact signLayerWithRoot ⟨0, by decide⟩ _ _ _
  · intro bottom
    refine Queries.bind (cost := 111589) (nextCost := 0) ?_ _ ?_
    · exact signUpper 151 1 (ri.2.toNat / 2) _ _ bottom.2 (by decide)
    · intro upper
      exact Queries.pure _

/-- Organizer-charge instance used by the atomic cutoff macro. -/
theorem signCompact (pk : PublicKey) (message : Message) :
    FixedCost ((SecurityIdealSign.signCompact pk message).liftComp GameWorld) 111596 :=
  (signCompact_queries pk message).fixedCost

/-- Serialization is pure and therefore the actual wire-signing interface has
the same fixed structural charge. -/
theorem signWire (pk : PublicKey) (message : Message) :
    FixedCost ((SecurityExperiment.signWire pk message).liftComp GameWorld) 111596 :=
  ((signCompact_queries pk message).map SecurityExperiment.serialize).fixedCost

end SigGolfCandidate.Hypertree.SecurityAtomicCounts
