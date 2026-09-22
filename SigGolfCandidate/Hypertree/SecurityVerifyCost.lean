import SigGolfCandidate.Hypertree.SecurityExperiment

namespace SigGolfCandidate.Hypertree.SecurityVerifyCost
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityGameHop
set_option backward.isDefEq.respectTransparency false

/-- Number of actual H queries of a deterministic oracle program, including hits
on previously cached inputs. The queried answer function controls all branches. -/
def calls {α : Type} (hash : Hash) (program : OracleComp HashSpec α) : Nat :=
  OracleComp.construct (fun _ => 0) (fun input _ next => next (hash input) + 1) program

@[simp] theorem calls_pure {α : Type} (hash : Hash) (value : α) : calls hash (pure value) = 0 := rfl

theorem calls_query_bind {α : Type} (hash : Hash) (input : Query)
    (next : BitVec 256 → OracleComp HashSpec α) :
    calls hash (liftM (HashSpec.query input) >>= next) = calls hash (next (hash input)) + 1 := rfl

theorem calls_bind {α β : Type} (hash : Hash) (program : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) :
    calls hash (program >>= next) = calls hash program + calls hash (next (evalWithAnswerFn hash program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, calls_query_bind, evalWithAnswerFn_bind]
    change calls hash (continuation (hash input) >>= next) + 1 =
      calls hash (continuation (hash input)) + 1 + calls hash (next (evalWithAnswerFn hash (continuation (hash input))))
    rw [ih]
    omega

@[simp] theorem calls_map {α β : Type} (hash : Hash) (f : α → β) (program : OracleComp HashSpec α) :
    calls hash (f <$> program) = calls hash program := by
  rw [map_eq_pure_bind, calls_bind]
  simp

@[simp] theorem calls_ask (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) :
    calls hash (SecurityReference.ask tag level tree leaf chain step payload) = 1 := rfl

@[simp] theorem calls_chainHash (hash : Hash) (level tree : Nat) (side : Bool)
    (chain : Chain) (step : Nat) (value : Digest) :
    calls hash (SecurityReference.chainHash level tree side chain step value) = 1 := by
  simp [SecurityReference.chainHash]

@[simp] theorem calls_node (hash : Hash) (level tree : Nat) (left right : Digest) :
    calls hash (SecurityReference.node level tree left right) = 1 := by simp [SecurityReference.node]

@[simp] theorem calls_compressLeaf (hash : Hash) (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    calls hash (SecurityReference.compressLeaf level tree side values) = 1 := by simp [SecurityReference.compressLeaf]

theorem calls_walk (hash : Hash) (level tree : Nat) (side : Bool) (chain : Chain)
    (start count : Nat) (value : Digest) :
    calls hash (SecurityReference.walk (SecurityReference.chainHash level tree side chain) start count value) = count := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih => simp [SecurityReference.walk, calls_bind, ih, Nat.add_comm]

theorem calls_sequenceFin {α : Type} (hash : Hash) (n : Nat) (body : Fin n → OracleComp HashSpec α) :
    calls hash (SecurityReference.sequenceFin n body) = ∑ i, calls hash (body i) := by
  induction n with
  | zero => simp [SecurityReference.sequenceFin]
  | succ n ih => simp [SecurityReference.sequenceFin, calls_bind, ih, Fin.sum_univ_succ]

/-- Exact verifier leaf HASH count; byte compression cost is a separate quantity. -/
def leafCalls (level : Nat) (message : Digest) : Nat :=
  if level = 0 then 1 else 1 + ∑ chain : Chain, (7 - (digit message chain).val)

theorem calls_recoverLeaf (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    calls hash (SecurityVerify.recoverLeaf level tree side message signature) = leafCalls level message := by
  by_cases bottom : level = 0 <;>
    simp [SecurityVerify.recoverLeaf, leafCalls, bottom, calls_bind, calls_sequenceFin, calls_walk,
      Nat.add_comm]

theorem calls_recoverLayer (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    calls hash (SecurityVerify.recoverLayer level tree side message signature) = leafCalls level message + 1 := by
  cases side <;> simp [SecurityVerify.recoverLayer, calls_bind, calls_recoverLeaf]

/-- Exact path count, evaluated on the recovered child root at each next layer. -/
def layersCalls (hash : Hash) : Nat → Nat → Digest → List LayerSignature → Nat
  | _, _, _, [] => 0
  | level, index, message, signature :: rest =>
      leafCalls level message + 1 + layersCalls hash (level + 1) (index / 2)
        (Reference.recoverLayer hash level (index / 2) (index % 2 == 1) message signature) rest

theorem calls_recoverLayers (hash : Hash) (level index : Nat) (message : Digest)
    (signatures : List LayerSignature) :
    calls hash (SecurityVerify.recoverLayers level index message signatures) =
      layersCalls hash level index message signatures := by
  induction signatures generalizing level index message with
  | nil => rfl
  | cons signature rest ih =>
    simp only [SecurityVerify.recoverLayers, calls_bind, calls_recoverLayer,
      SecurityVerify.eval_recoverLayer, ih, layersCalls]

def verifyCalls (hash : Hash) (pk : PublicKey) (message : Message) (signature : Compact) : Nat :=
  1 + layersCalls hash 0 (Reference.indexOf hash pk message signature.randomizer).toNat 0 signature.toReference.layers

theorem calls_verifyCompact (hash : Hash) (pk : PublicKey) (message : Message) (signature : Compact) :
    calls hash (SecurityVerify.verifyCompact pk message signature) = verifyCalls hash pk message signature := by
  simp [SecurityVerify.verifyCompact, calls_bind, calls_recoverLayers, verifyCalls, Reference.indexOf]

/-- The fixed-H count above is exactly the security experiment's charged count
when the public reference program is lifted into its actual game interface. -/
theorem counted_lift {α : Type} (hash : Hash) (gameAnswers : QueryImpl GameWorld Id)
    (publicAgree : ∀ input, gameAnswers (.inr (.inr input)) = hash input)
    (program : OracleComp HashSpec α) :
    evalWithAnswerFn gameAnswers (SecurityBudget.counted (program.liftComp GameWorld)) =
      (evalWithAnswerFn hash program, calls hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
    have step : (liftM (HashSpec.query input) >>= next).liftComp GameWorld =
        (do let answer ← liftM (GameWorld.query (.inr (.inr input)))
            (next answer).liftComp GameWorld) := by
      rw [OracleComp.liftComp_bind]
      rfl
    rw [step, SecurityBudget.counted_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    have queried : evalWithAnswerFn gameAnswers (liftM (GameWorld.query (.inr (.inr input)))) =
        hash input := publicAgree input
    rw [queried, ih]
    rfl

theorem counted_verifyCompact (hash : Hash) (gameAnswers : QueryImpl GameWorld Id)
    (publicAgree : ∀ input, gameAnswers (.inr (.inr input)) = hash input)
    (pk : PublicKey) (message : Message) (signature : Compact) :
    (evalWithAnswerFn gameAnswers
      (SecurityBudget.counted ((SecurityVerify.verifyCompact pk message signature).liftComp GameWorld))).2 =
        verifyCalls hash pk message signature := by
  rw [counted_lift hash gameAnswers publicAgree, calls_verifyCompact]


end SigGolfCandidate.Hypertree.SecurityVerifyCost
