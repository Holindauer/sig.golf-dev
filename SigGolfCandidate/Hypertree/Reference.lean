import SigGolfCandidate.Hypertree.Proofs

namespace SigGolfCandidate.Hypertree.Reference
open SigGolf

abbrev Digest := Bytes 16
abbrev Chain := Fin 46

/-- Little-endian packing with the length retained in the oracle input. -/
def packed (data : List Byte) : Query :=
  ⟨8 * data.length, BitVec.ofNat (8 * data.length)
    (data.zipIdx.foldl (fun acc entry => acc + entry.1.toNat * 2 ^ (8 * entry.2)) 0)⟩

/-- The exact 32-byte domain header used by the bytecode. -/
def query (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) : BitVec 256 :=
  let header : BitVec 64 := BitVec.ofNat 64
    (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32)
  hash (packed (bytes (n := 8) header ++ bytes (n := 24) (BitVec.ofNat 192 tree) ++ payload))

def truncate (value : BitVec 256) : Digest := value.extractLsb' 0 128

def sideNumber (side : Bool) : Nat := if side then 1 else 0

def messageDigit (message : Digest) (i : Fin 43) : Nat := message.toNat / 8 ^ i.val % 8

def checksum (message : Digest) : Nat := 301 - ∑ i : Fin 43, messageDigit message i

def digit (message : Digest) (i : Chain) : Fin 8 :=
  ⟨(if i.val < 43 then message.toNat / 8 ^ i.val
    else checksum message / 8 ^ (i.val - 43)) % 8, Nat.mod_lt _ (by decide)⟩

def secret (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool) (chain : Chain) : Digest :=
  truncate (query hash 1 level tree (sideNumber side) chain.val 0 (bytes seed))

def chainHash (hash : Hash) (level tree : Nat) (side : Bool) (chain : Chain)
    (step : Nat) (value : Digest) : Digest :=
  truncate (query hash 2 level tree (sideNumber side) chain.val step (bytes value))

def endpoint (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool) (chain : Chain) : Digest :=
  walk (chainHash hash level tree side chain) 0 7 (secret hash seed level tree side chain)

def compressLeaf (hash : Hash) (level tree : Nat) (side : Bool) (values : Chain → Digest) : Digest :=
  truncate (query hash 3 level tree (sideNumber side) 0 0
    ((List.ofFn values).flatMap fun value => bytes value))

def leafRoot (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool) : Digest :=
  if level = 0 then
    chainHash hash level tree side 0 0 (secret hash seed level tree side 0)
  else compressLeaf hash level tree side (endpoint hash seed level tree side)

def node (hash : Hash) (level tree : Nat) (left right : Digest) : Digest :=
  truncate (query hash 4 level tree 0 0 0 (bytes left ++ bytes right))

def treeRoot (hash : Hash) (seed : Seed) (level tree : Nat) : Digest :=
  node hash level tree (leafRoot hash seed level tree false) (leafRoot hash seed level tree true)

structure LayerSignature where
  values : Chain → Digest
  sibling : Digest

/-- At level zero only values[0] is serialized. Other levels serialize all 46 values. -/
def signLayer (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool)
    (message : Digest) : LayerSignature where
  values := fun chain => if level = 0 then secret hash seed level tree side chain
    else walk (chainHash hash level tree side chain) 0 (digit message chain).val
      (secret hash seed level tree side chain)
  sibling := leafRoot hash seed level tree (!side)

def recoverLeaf (hash : Hash) (level tree : Nat) (side : Bool) (message : Digest)
    (signature : LayerSignature) : Digest :=
  if level = 0 then chainHash hash level tree side 0 0 (signature.values 0)
  else compressLeaf hash level tree side (fun chain =>
    walk (chainHash hash level tree side chain) (digit message chain).val
      (7 - (digit message chain).val) (signature.values chain))

def recoverLayer (hash : Hash) (level tree : Nat) (side : Bool) (message : Digest)
    (signature : LayerSignature) : Digest :=
  let current := recoverLeaf hash level tree side message signature
  if side then node hash level tree signature.sibling current
  else node hash level tree current signature.sibling

theorem recover_sign_leaf (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool)
    (message : Digest) :
    recoverLeaf hash level tree side message (signLayer hash seed level tree side message) =
      leafRoot hash seed level tree side := by
  by_cases h : level = 0
  · simp [recoverLeaf, signLayer, leafRoot, h]
  · simp only [recoverLeaf, signLayer, leafRoot, h, ↓reduceIte]
    congr 1
    funext chain
    exact recover_chain _ _ _

theorem recover_sign_layer (hash : Hash) (seed : Seed) (level tree : Nat) (side : Bool)
    (message : Digest) :
    recoverLayer hash level tree side message (signLayer hash seed level tree side message) =
      treeRoot hash seed level tree := by
  simp only [recoverLayer, recover_sign_leaf]
  cases side <;> rfl

def signLayers (hash : Hash) (seed : Seed) : Nat → Nat → Nat → Digest → List LayerSignature
  | 0, _, _, _ => []
  | count + 1, level, index, message =>
      signLayer hash seed level (index / 2) (index % 2 == 1) message ::
        signLayers hash seed count (level + 1) (index / 2) (treeRoot hash seed level (index / 2))

def recoverLayers (hash : Hash) : Nat → Nat → Digest → List LayerSignature → Digest
  | _, _, message, [] => message
  | level, index, message, signature :: rest =>
      recoverLayers hash (level + 1) (index / 2)
        (recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest

def rootsAfter (hash : Hash) (seed : Seed) : Nat → Nat → Nat → Digest → Digest
  | 0, _, _, message => message
  | count + 1, level, index, _ =>
      rootsAfter hash seed count (level + 1) (index / 2) (treeRoot hash seed level (index / 2))

theorem recover_sign_layers (hash : Hash) (seed : Seed) (count level index : Nat) (message : Digest) :
    recoverLayers hash level index message (signLayers hash seed count level index message) =
      rootsAfter hash seed count level index message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [signLayers, recoverLayers, recover_sign_layer, rootsAfter]
    exact ih _ _ _

theorem roots_after_succ (hash : Hash) (seed : Seed) (count level index : Nat) (message : Digest) :
    rootsAfter hash seed (count + 1) level index message =
      treeRoot hash seed (level + count) (index / 2 ^ (count + 1)) := by
  induction count generalizing level index message with
  | zero => simp [rootsAfter]
  | succ count ih =>
    rw [rootsAfter, ih]
    simp [Nat.div_div_eq_div_mul, pow_succ, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_comm]

def randomizer (hash : Hash) (seed : Seed) (message : Message) : Bytes 32 :=
  query hash 6 0 0 0 0 0 (bytes seed ++ bytes message)

def indexOf (hash : Hash) (pk : PublicKey) (message : Message) (r : Bytes 32) : BitVec 160 :=
  (query hash 5 0 0 0 0 0 (bytes pk ++ bytes message ++ bytes r)).extractLsb' 0 160

def keygen (hash : Hash) (seed : Seed) : PublicKey := treeRoot hash seed 159 0

structure Signature where
  randomizer : Bytes 32
  layers : List LayerSignature

def sign (hash : Hash) (seed : Seed) (pk : PublicKey) (message : Message) : Signature :=
  let r := randomizer hash seed message
  ⟨r, signLayers hash seed 160 0 (indexOf hash pk message r).toNat 0⟩

def verify (hash : Hash) (pk : PublicKey) (message : Message) (signature : Signature) : Prop :=
  signature.layers.length = 160 ∧
    recoverLayers hash 0 (indexOf hash pk message signature.randomizer).toNat 0 signature.layers = pk

theorem sign_layers_length (hash : Hash) (seed : Seed) (count level index : Nat) (message : Digest) :
    (signLayers hash seed count level index message).length = count := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih => simp [signLayers, ih]

/-- Functional correctness for every seed, message, and fixed oracle. No probabilistic or collision-resistance assumption is used. This does not yet establish bytecode refinement. -/
theorem correct (hash : Hash) (seed : Seed) (message : Message) :
    verify hash (keygen hash seed) message (sign hash seed (keygen hash seed) message) := by
  constructor
  · exact sign_layers_length _ _ _ _ _ _
  · change recoverLayers hash 0 (indexOf hash (keygen hash seed) message (randomizer hash seed message)).toNat 0
      (signLayers hash seed 160 0 (indexOf hash (keygen hash seed) message (randomizer hash seed message)).toNat 0) = _
    rw [recover_sign_layers, roots_after_succ hash seed 159 0]
    have hidx := (indexOf hash (keygen hash seed) message (randomizer hash seed message)).isLt
    simp only [Nat.zero_add, Nat.div_eq_of_lt hidx]
    rfl

/-- info: 'SigGolfCandidate.Hypertree.Reference.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms correct

end SigGolfCandidate.Hypertree.Reference
