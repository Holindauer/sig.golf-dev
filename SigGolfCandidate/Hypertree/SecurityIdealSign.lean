import SigGolfCandidate.Hypertree.SecurityIdealKeygen

namespace SigGolfCandidate.Hypertree.SecurityIdealSign
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityIdealKeygen
open SignatureEncoding

def randomizer (message : Message) : OracleComp SplitWorld (Bytes 32) :=
  liftM (SecretSpec.query (.randomizer message))

@[simp] theorem simulate_randomizer (seed : Seed) (message : Message) :
    simulateQ (realImplementation seed) (randomizer message) =
      (liftM (HashSpec.query (SecurityRandomOracle.randomizerInput seed message)) :
        OracleComp HashSpec (Bytes 32)) := by
  simp only [randomizer, realImplementation, QueryImpl.simulateQ_add_liftM_query_left]
  rfl

def randomizedIndex (pk : PublicKey) (message : Message) :
    OracleComp SplitWorld (Bytes 32 × BitVec 160) := do
  let r ← randomizer message
  let answer ← publicCall (liftM (HashSpec.query (SecurityRandomOracle.indexInput pk message r)))
  return (r, answer.extractLsb' 0 160)

@[simp] theorem simulate_randomizedIndex (seed : Seed) (pk : PublicKey) (message : Message) :
    simulateQ (realImplementation seed) (randomizedIndex pk message) =
      SecurityRandomOracle.randomizedIndex seed pk message := by
  simp [randomizedIndex, SecurityRandomOracle.randomizedIndex]

def signChain (address : ChainAddress) (message : Digest) :
    OracleComp SplitWorld (Digest × Digest) := do
  let value ← secret address
  let fragment ← publicCall (SecurityReference.walk
    (SecurityReference.chainHash address.level.val address.tree.toNat address.side address.chain)
    0 (digit message address.chain).val value)
  let last ← publicCall (SecurityReference.walk
    (SecurityReference.chainHash address.level.val address.tree.toNat address.side address.chain)
    (digit message address.chain).val (7 - (digit message address.chain).val) fragment)
  return (fragment, last)

@[simp] theorem simulate_signChain (seed : Seed) (address : ChainAddress) (message : Digest) :
    simulateQ (realImplementation seed) (signChain address message) =
      SecurityReference.signChain seed address.level.val address.tree.toNat address.side message address.chain := by
  simp [signChain, SecurityReference.signChain]

def signLayerWithRoot (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) :
    OracleComp SplitWorld (LayerSignature × Digest) := do
  if level.val = 0 then
    let fragment ← secret ⟨level, tree, side, 0⟩
    let current ← publicCall (SecurityReference.chainHash level.val tree.toNat side 0 0 fragment)
    let sibling ← leafRoot level tree (!side)
    let root ← publicCall (if side then SecurityReference.node level.val tree.toNat sibling current
      else SecurityReference.node level.val tree.toNat current sibling)
    return (⟨fun i => if i = 0 then fragment else 0, sibling⟩, root)
  else
    let chains ← sequenceFin 46 (fun chain => signChain ⟨level, tree, side, chain⟩ message)
    let current ← publicCall (SecurityReference.compressLeaf level.val tree.toNat side (fun i => (chains i).2))
    let sibling ← leafRoot level tree (!side)
    let root ← publicCall (if side then SecurityReference.node level.val tree.toNat sibling current
      else SecurityReference.node level.val tree.toNat current sibling)
    return (⟨fun i => (chains i).1, sibling⟩, root)

@[simp] theorem simulate_signLayerWithRoot (seed : Seed) (level : Fin 160) (tree : BitVec 192)
    (side : Bool) (message : Digest) :
    simulateQ (realImplementation seed) (signLayerWithRoot level tree side message) =
      SecurityReference.signLayerWithRoot seed level.val tree.toNat side message := by
  by_cases zero : level.val = 0 <;> cases side <;>
    simp [signLayerWithRoot, SecurityReference.signLayerWithRoot, zero]

/-- Only valid private addresses occur. The recursive level bound is explicit,
while the tree identifier is reduced at every step of the actual signer. -/
def signUpper : (count level index : Nat) → count + level ≤ 160 → index < 2 ^ 192 →
    Digest → OracleComp SplitWorld (List LayerSignature)
  | 0, _, _, _, _, _ => pure []
  | count + 1, level, index, hl, hi, message => do
      let layer ← signLayerWithRoot ⟨level, by omega⟩
        (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message
      let rest ← signUpper count (level + 1) (index / 2) (by omega)
        (lt_of_le_of_lt (Nat.div_le_self ..) hi) layer.2
      return layer.1 :: rest

@[simp] theorem simulate_signUpper (seed : Seed) (count level index : Nat)
    (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    simulateQ (realImplementation seed) (signUpper count level index hl hi message) =
      SecurityReference.signUpper seed count level index message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    have half : index / 2 < 2 ^ 192 := lt_of_le_of_lt (Nat.div_le_self ..) hi
    simp only [signUpper, SecurityReference.signUpper, simulateQ_bind, simulateQ_pure,
      simulate_signLayerWithRoot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt half, ih]

private theorem index_bound (index : BitVec 160) : index.toNat / 2 < 2 ^ 192 := by
  have h := index.isLt
  have hpow : (2 : Nat) ^ 160 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
  exact lt_of_le_of_lt (Nat.div_le_self ..) (lt_of_lt_of_le h hpow)

/-- Seedless signing program using independent private derivation slots. -/
def signCompact (pk : PublicKey) (message : Message) : OracleComp SplitWorld Compact := do
  let ri ← randomizedIndex pk message
  let bottom ← signLayerWithRoot ⟨0, by decide⟩ (BitVec.ofNat 192 (ri.2.toNat / 2))
    (ri.2.toNat % 2 == 1) 0
  let upper ← signUpper 159 1 (ri.2.toNat / 2) (by decide) (index_bound ri.2) bottom.2
  return ⟨ri.1, bottom.1.values 0, bottom.1.sibling, upper⟩

/-- Exact equality of oracle computations, including repeated queries and their
order, connects full signing to the real/ideal cache separation theorem. -/
theorem simulate_signCompact (seed : Seed) (pk : PublicKey) (message : Message) :
    simulateQ (realImplementation seed) (signCompact pk message) =
      SecurityReference.signCompact seed pk message := by
  simp only [signCompact, SecurityReference.signCompact, simulateQ_bind, simulateQ_pure,
    simulate_randomizedIndex, simulate_signLayerWithRoot, simulate_signUpper,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (index_bound _)]

/-- The list length is structural and holds for independent private/public answers,
not only for answer functions arising from a real seeded oracle. -/
theorem eval_signUpper_length (answers : QueryImpl SplitWorld Id) (count level index : Nat)
    (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    (evalWithAnswerFn answers (signUpper count level index hl hi message)).length = count := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [signUpper, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons, ih]

/-- Every fixed independent-oracle interpretation produces a valid compact object. -/
theorem eval_signCompact_valid (answers : QueryImpl SplitWorld Id) (pk : PublicKey) (message : Message) :
    (evalWithAnswerFn answers (signCompact pk message)).Valid := by
  simp only [signCompact, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Compact.Valid,
    eval_signUpper_length]

end SigGolfCandidate.Hypertree.SecurityIdealSign
