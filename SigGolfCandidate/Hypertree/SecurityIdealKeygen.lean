import SigGolfCandidate.Hypertree.SecurityDerivation

namespace SigGolfCandidate.Hypertree.SecurityIdealKeygen
open SigGolf OracleComp OracleSpec Reference SecurityDerivation

/-- Public computations are forwarded unchanged into the two-oracle scheme. -/
def publicCall {α : Type} (program : OracleComp HashSpec α) : OracleComp SplitWorld α :=
  program.liftComp SplitWorld

@[simp] theorem simulate_public {α : Type} (secretKey : SecretKey) (program : OracleComp HashSpec α) :
    simulateQ (realImplementation secretKey) (publicCall program) = program := by
  simp [publicCall, realImplementation, QueryImpl.simulateQ_add_liftM_right, QueryImpl.simulateQ_toQueryImpl]

def sequenceFin {α : Type} : (n : Nat) → (Fin n → OracleComp SplitWorld α) →
    OracleComp SplitWorld (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, body => do
      let head ← body 0
      let tail ← sequenceFin n (fun i => body i.succ)
      return Fin.cases head tail

@[simp] theorem simulate_sequenceFin {α : Type} (secretKey : SecretKey) (n : Nat)
    (body : Fin n → OracleComp SplitWorld α) :
    simulateQ (realImplementation secretKey) (sequenceFin n body) =
      SecurityReference.sequenceFin n (fun i => simulateQ (realImplementation secretKey) (body i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sequenceFin, SecurityReference.sequenceFin, ih]

def secret (address : ChainAddress) : OracleComp SplitWorld Digest :=
  Reference.truncate <$> (liftM (SecretSpec.query (.chain address)) : OracleComp SplitWorld (BitVec 256))

@[simp] theorem simulate_secret (secretKey : SecretKey) (address : ChainAddress) :
    simulateQ (realImplementation secretKey) (secret address) =
      SecurityReference.secret secretKey address.level.val address.tree.toNat address.side address.chain := by
  simp only [secret, simulateQ_map, realImplementation,
    QueryImpl.simulateQ_add_liftM_query_left]
  rfl

def endpoint (address : ChainAddress) : OracleComp SplitWorld Digest := do
  let value ← secret address
  publicCall (SecurityReference.walk
    (SecurityReference.chainHash address.level.val address.tree.toNat address.side address.chain) 0 7 value)

@[simp] theorem simulate_endpoint (secretKey : SecretKey) (address : ChainAddress) :
    simulateQ (realImplementation secretKey) (endpoint address) =
      SecurityReference.endpoint secretKey address.level.val address.tree.toNat address.side address.chain := by
  simp [endpoint, SecurityReference.endpoint]

def leafRoot (level : Fin 160) (tree : BitVec 192) (side : Bool) : OracleComp SplitWorld Digest := do
  if level.val = 0 then
    let value ← secret ⟨level, tree, side, 0⟩
    publicCall (SecurityReference.chainHash level.val tree.toNat side 0 0 value)
  else
    let values ← sequenceFin 46 (fun chain => endpoint ⟨level, tree, side, chain⟩)
    publicCall (SecurityReference.compressLeaf level.val tree.toNat side values)

@[simp] theorem simulate_leafRoot (secretKey : SecretKey) (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    simulateQ (realImplementation secretKey) (leafRoot level tree side) =
      SecurityReference.leafRoot secretKey level.val tree.toNat side := by
  by_cases zero : level.val = 0 <;>
    simp [leafRoot, SecurityReference.leafRoot, zero]

def treeRoot (level : Fin 160) (tree : BitVec 192) : OracleComp SplitWorld Digest := do
  let left ← leafRoot level tree false
  let right ← leafRoot level tree true
  publicCall (SecurityReference.node level.val tree.toNat left right)

@[simp] theorem simulate_treeRoot (secretKey : SecretKey) (level : Fin 160) (tree : BitVec 192) :
    simulateQ (realImplementation secretKey) (treeRoot level tree) =
      SecurityReference.treeRoot secretKey level.val tree.toNat := by
  simp [treeRoot, SecurityReference.treeRoot]

/-- The ideal key generator contains no secret key. Only the interpretation of private
slots distinguishes the real secretKeyed implementation from the independent ideal one. -/
def keygen : OracleComp SplitWorld PublicKey := treeRoot ⟨159, by decide⟩ 0

/-- Syntactic oracle-computation equality, stronger than fixed-H output equality:
this factors the actual monadic reference key generator through private slots. -/
theorem simulate_keygen (secretKey : SecretKey) :
    simulateQ (realImplementation secretKey) keygen = SecurityReference.keygen secretKey := by
  exact simulate_treeRoot secretKey ⟨159, by decide⟩ 0

end SigGolfCandidate.Hypertree.SecurityIdealKeygen
