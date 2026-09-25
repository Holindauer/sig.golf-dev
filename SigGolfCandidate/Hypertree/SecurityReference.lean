import SigGolfCandidate.Hypertree.SecurityRandomOracle
import SigGolfCandidate.Hypertree.Signature

namespace SigGolfCandidate.Hypertree.SecurityReference
open SigGolf OracleComp OracleSpec Reference SignatureEncoding

/-- Sequence a fixed family without evaluating unused bottom-layer fields. -/
def sequenceFin {α : Type} : (n : Nat) → (Fin n → OracleComp HashSpec α) →
    OracleComp HashSpec (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, body => do
      let head ← body 0
      let tail ← sequenceFin n (fun i => body i.succ)
      return Fin.cases head tail

theorem eval_sequenceFin {α : Type} (hash : Hash) (n : Nat)
    (body : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn hash (sequenceFin n body) = fun i => evalWithAnswerFn hash (body i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def ask (tag level tree leaf chain step : Nat) (payload : List Byte) :
    OracleComp HashSpec (BitVec 256) :=
  liftM (HashSpec.query (SecurityRandomOracle.addressedInput tag level tree leaf chain step payload))

@[simp] theorem eval_ask (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) :
    evalWithAnswerFn hash (ask tag level tree leaf chain step payload) =
      Reference.query hash tag level tree leaf chain step payload := rfl

def secret (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) : OracleComp HashSpec Digest :=
  Reference.truncate <$> ask 1 level tree (sideNumber side) chain.val 0 (bytes secretKey)

def chainHash (level tree : Nat) (side : Bool) (chain : Chain) (step : Nat) (value : Digest) :
    OracleComp HashSpec Digest :=
  Reference.truncate <$> ask 2 level tree (sideNumber side) chain.val step (bytes value)

def walk {α : Type} (hash : Nat → α → OracleComp HashSpec α) (start : Nat) : Nat → α → OracleComp HashSpec α
  | 0, value => pure value
  | count + 1, value => do
      let value' ← hash start value
      walk hash (start + 1) count value'

theorem eval_walk {α : Type} (hash : Hash) (body : Nat → α → OracleComp HashSpec α)
    (start count : Nat) (value : α) :
    evalWithAnswerFn hash (walk body start count value) =
      Hypertree.walk (fun step x => evalWithAnswerFn hash (body step x)) start count value := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih => simp only [walk, evalWithAnswerFn_bind, ih, Hypertree.walk]

@[simp] theorem eval_secret (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    evalWithAnswerFn hash (secret secretKey level tree side chain) =
      Reference.secret hash secretKey level tree side chain := by simp [secret, Reference.secret]

@[simp] theorem eval_chainHash (hash : Hash) (level tree : Nat) (side : Bool) (chain : Chain)
    (step : Nat) (value : Digest) :
    evalWithAnswerFn hash (chainHash level tree side chain step value) =
      Reference.chainHash hash level tree side chain step value := by
  simp [chainHash, Reference.chainHash]

def endpoint (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) : OracleComp HashSpec Digest := do
  let value ← secret secretKey level tree side chain
  walk (chainHash level tree side chain) 0 7 value

@[simp] theorem eval_endpoint (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    evalWithAnswerFn hash (endpoint secretKey level tree side chain) =
      Reference.endpoint hash secretKey level tree side chain := by
  simp [endpoint, eval_walk, Reference.endpoint]

def compressLeaf (level tree : Nat) (side : Bool) (values : Chain → Digest) : OracleComp HashSpec Digest :=
  Reference.truncate <$> ask 3 level tree (sideNumber side) 0 0
    ((List.ofFn values).flatMap fun value => bytes value)

@[simp] theorem eval_compressLeaf (hash : Hash) (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    evalWithAnswerFn hash (compressLeaf level tree side values) =
      Reference.compressLeaf hash level tree side values := by
  simp [compressLeaf, Reference.compressLeaf]

def leafRoot (secretKey : SecretKey) (level tree : Nat) (side : Bool) : OracleComp HashSpec Digest := do
  if level = 0 then
    let value ← secret secretKey level tree side 0
    chainHash level tree side 0 0 value
  else
    let values ← sequenceFin 46 (endpoint secretKey level tree side)
    compressLeaf level tree side values

@[simp] theorem eval_leafRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) :
    evalWithAnswerFn hash (leafRoot secretKey level tree side) =
      Reference.leafRoot hash secretKey level tree side := by
  by_cases zero : level = 0
  · simp [leafRoot, Reference.leafRoot, zero]
  · simp [leafRoot, Reference.leafRoot, zero, eval_sequenceFin]

def node (level tree : Nat) (left right : Digest) : OracleComp HashSpec Digest :=
  Reference.truncate <$> ask 4 level tree 0 0 0 (bytes left ++ bytes right)

@[simp] theorem eval_node (hash : Hash) (level tree : Nat) (left right : Digest) :
    evalWithAnswerFn hash (node level tree left right) = Reference.node hash level tree left right := by
  simp [node, Reference.node]

def treeRoot (secretKey : SecretKey) (level tree : Nat) : OracleComp HashSpec Digest := do
  let left ← leafRoot secretKey level tree false
  let right ← leafRoot secretKey level tree true
  node level tree left right

@[simp] theorem eval_treeRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) :
    evalWithAnswerFn hash (treeRoot secretKey level tree) = Reference.treeRoot hash secretKey level tree := by
  simp [treeRoot, Reference.treeRoot]

/-- This monadic key generator uses actual `HashSpec` inputs, so its random-oracle
meaning is the organizer's `withRandomOracle`, not an assumed random root. -/
def keygen (secretKey : SecretKey) : OracleComp HashSpec PublicKey := treeRoot secretKey 159 0

@[simp] theorem eval_keygen (hash : Hash) (secretKey : SecretKey) :
    evalWithAnswerFn hash (keygen secretKey) = Reference.keygen hash secretKey :=
  eval_treeRoot hash secretKey 159 0

/-- Generate a WOTS fragment and finish the same chain, reusing all prior work. -/
def signChain (secretKey : SecretKey) (level tree : Nat) (side : Bool) (message : Digest) (chain : Chain) :
    OracleComp HashSpec (Digest × Digest) := do
  let value ← secret secretKey level tree side chain
  let fragment ← walk (chainHash level tree side chain) 0 (digit message chain).val value
  let last ← walk (chainHash level tree side chain) (digit message chain).val
    (7 - (digit message chain).val) fragment
  return (fragment, last)

@[simp] theorem eval_signChain (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (chain : Chain) :
    evalWithAnswerFn hash (signChain secretKey level tree side message chain) =
      (Hypertree.walk (Reference.chainHash hash level tree side chain) 0 (digit message chain).val
        (Reference.secret hash secretKey level tree side chain),
       Reference.endpoint hash secretKey level tree side chain) := by
  simp [signChain, eval_walk, Reference.endpoint, recover_chain]

/-- Only the bottom entry actually carried on the wire is retained. -/
def canonicalLayer (level : Nat) (signature : LayerSignature) : LayerSignature :=
  if level = 0 then ⟨fun i => if i = 0 then signature.values 0 else 0, signature.sibling⟩
  else signature

/-- The signer computes each subtree root while producing its layer signature.
This shares chain work and avoids re-querying the full tree after signing. -/
def signLayerWithRoot (secretKey : SecretKey) (level tree : Nat) (side : Bool) (message : Digest) :
    OracleComp HashSpec (LayerSignature × Digest) := do
  if level = 0 then
    let fragment ← secret secretKey level tree side 0
    let current ← chainHash level tree side 0 0 fragment
    let sibling ← leafRoot secretKey level tree (!side)
    let root ← if side then node level tree sibling current else node level tree current sibling
    return (⟨fun i => if i = 0 then fragment else 0, sibling⟩, root)
  else
    let chains ← sequenceFin 46 (signChain secretKey level tree side message)
    let current ← compressLeaf level tree side (fun i => (chains i).2)
    let sibling ← leafRoot secretKey level tree (!side)
    let root ← if side then node level tree sibling current else node level tree current sibling
    return (⟨fun i => (chains i).1, sibling⟩, root)

@[simp] theorem eval_signLayerWithRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) :
    evalWithAnswerFn hash (signLayerWithRoot secretKey level tree side message) =
      (canonicalLayer level (Reference.signLayer hash secretKey level tree side message),
        Reference.treeRoot hash secretKey level tree) := by
  by_cases zero : level = 0
  · subst level
    cases side <;>
      simp [signLayerWithRoot, canonicalLayer, Reference.signLayer, Reference.treeRoot, Reference.leafRoot]
  · cases side <;>
      simp [signLayerWithRoot, canonicalLayer, Reference.signLayer, Reference.treeRoot,
        Reference.leafRoot, zero, eval_sequenceFin]

def signUpper (secretKey : SecretKey) : Nat → Nat → Nat → Digest → OracleComp HashSpec (List LayerSignature)
  | 0, _, _, _ => pure []
  | count + 1, level, index, message => do
      let layer ← signLayerWithRoot secretKey level (index / 2) (index % 2 == 1) message
      let rest ← signUpper secretKey count (level + 1) (index / 2) layer.2
      return layer.1 :: rest

theorem eval_signUpper (hash : Hash) (secretKey : SecretKey) (count level index : Nat) (message : Digest)
    (positive : 0 < level) :
    evalWithAnswerFn hash (signUpper secretKey count level index message) =
      Reference.signLayers hash secretKey count level index message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    have nonzero : level ≠ 0 := by omega
    simp only [signUpper, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_signLayerWithRoot,
      canonicalLayer, nonzero, ↓reduceIte, Reference.signLayers]
    rw [ih _ _ _ (by omega)]

/-- Actual compact signing. Bottom values absent from the wire are never queried. -/
def signCompact (secretKey : SecretKey) (pk : PublicKey) (message : Message) : OracleComp HashSpec Compact := do
  let ri ← SecurityRandomOracle.randomizedIndex secretKey pk message
  let bottom ← signLayerWithRoot secretKey 0 (ri.2.toNat / 2) (ri.2.toNat % 2 == 1) 0
  let upper ← signUpper secretKey 159 1 (ri.2.toNat / 2) bottom.2
  return ⟨ri.1, bottom.1.values 0, bottom.1.sibling, upper⟩

@[simp] theorem eval_signCompact (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    evalWithAnswerFn hash (signCompact secretKey pk message) =
      SignatureEncoding.signCompact hash secretKey pk message := by
  simp only [signCompact, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    SecurityRandomOracle.eval_randomizedIndex, eval_signLayerWithRoot,
    eval_signUpper hash secretKey 159 1 _ _ (by decide), canonicalLayer, ↓reduceIte,
    SignatureEncoding.signCompact, Compact.ofReference, Reference.sign, Reference.signLayers,
    List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero]


end SigGolfCandidate.Hypertree.SecurityReference
