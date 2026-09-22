import SigGolfCandidate.Hypertree.SecurityReference

namespace SigGolfCandidate.Hypertree.SecurityVerify
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityReference

/-- Recover precisely the leaf consumed by the reference verifier. -/
def recoverLeaf (level tree : Nat) (side : Bool) (message : Digest) (signature : LayerSignature) :
    OracleComp HashSpec Digest := do
  if level = 0 then
    SecurityReference.chainHash level tree side 0 0 (signature.values 0)
  else
    let values ← sequenceFin 46 (fun chain =>
      SecurityReference.walk (SecurityReference.chainHash level tree side chain)
        (digit message chain).val (7 - (digit message chain).val) (signature.values chain))
    SecurityReference.compressLeaf level tree side values

@[simp] theorem eval_recoverLeaf (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    evalWithAnswerFn hash (recoverLeaf level tree side message signature) =
      Reference.recoverLeaf hash level tree side message signature := by
  by_cases zero : level = 0
  · simp [recoverLeaf, Reference.recoverLeaf, zero]
  · simp [recoverLeaf, Reference.recoverLeaf, zero, eval_sequenceFin, eval_walk]

def recoverLayer (level tree : Nat) (side : Bool) (message : Digest) (signature : LayerSignature) :
    OracleComp HashSpec Digest := do
  let current ← recoverLeaf level tree side message signature
  if side then SecurityReference.node level tree signature.sibling current
  else SecurityReference.node level tree current signature.sibling

@[simp] theorem eval_recoverLayer (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    evalWithAnswerFn hash (recoverLayer level tree side message signature) =
      Reference.recoverLayer hash level tree side message signature := by
  cases side <;> simp [recoverLayer, Reference.recoverLayer]

def recoverLayers : Nat → Nat → Digest → List LayerSignature → OracleComp HashSpec Digest
  | _, _, message, [] => pure message
  | level, index, message, signature :: rest => do
      let root ← recoverLayer level (index / 2) (index % 2 == 1) message signature
      recoverLayers (level + 1) (index / 2) root rest

@[simp] theorem eval_recoverLayers (hash : Hash) (level index : Nat) (message : Digest)
    (signatures : List LayerSignature) :
    evalWithAnswerFn hash (recoverLayers level index message signatures) =
      Reference.recoverLayers hash level index message signatures := by
  induction signatures generalizing level index message with
  | nil => rfl
  | cons signature rest ih =>
    simp only [recoverLayers, evalWithAnswerFn_bind, eval_recoverLayer, ih, Reference.recoverLayers]

/-- Verification makes only public H queries. In particular it does not recompute
or validate the signer-secret randomizer; any supplied 256-bit randomizer is handled. -/
def verifyCompact (pk : PublicKey) (message : Message) (signature : Compact) : OracleComp HashSpec Bool := do
  let answer ← ask 5 0 0 0 0 0 (bytes pk ++ bytes message ++ bytes signature.randomizer)
  let index := answer.extractLsb' 0 160
  let root ← recoverLayers 0 index.toNat 0 signature.toReference.layers
  return decide (signature.toReference.layers.length = 160 ∧ root = pk)

/-- Exact acceptance semantics for arbitrary compact signatures and arbitrary H. -/
theorem eval_verifyCompact_iff (hash : Hash) (pk : PublicKey) (message : Message) (signature : Compact) :
    evalWithAnswerFn hash (verifyCompact pk message signature) = true ↔
      Reference.verify hash pk message signature.toReference := by
  simp [verifyCompact, Reference.verify, Reference.indexOf, Compact.toReference]

/-- The monadic reference pipeline accepts for every fixed oracle and seed. -/
theorem correct (hash : Hash) (seed : Seed) (message : Message) :
    evalWithAnswerFn hash (do
      let pk ← SecurityReference.keygen seed
      let signature ← SecurityReference.signCompact seed pk message
      verifyCompact pk message signature) = true := by
  simp only [evalWithAnswerFn_bind, eval_keygen, eval_signCompact]
  exact (eval_verifyCompact_iff hash (Reference.keygen hash seed) message
    (SignatureEncoding.signCompact hash seed (Reference.keygen hash seed) message)).mpr
      (signCompact_correct hash seed message)

end SigGolfCandidate.Hypertree.SecurityVerify
