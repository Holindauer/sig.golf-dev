import SigGolfCandidate.Hypertree.SecurityGraphExtraction
import SigGolfCandidate.Hypertree.SecurityTrace
import SigGolfCandidate.Hypertree.SecurityVerifyCost

namespace SigGolfCandidate.Hypertree.SecurityVerifyTrace
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Exact deterministic hash-input trace, including repeated and cached queries.
Answers are the values of the same total oracle controlling execution. -/
def queries {α : Type} (hash : Hash) (program : OracleComp HashSpec α) : List Query :=
  OracleComp.construct (fun _ => []) (fun input _ next => input :: next (hash input)) program

@[simp] theorem queries_pure {α : Type} (hash : Hash) (value : α) : queries hash (pure value) = [] := rfl

theorem queries_query_bind {α : Type} (hash : Hash) (input : Query)
    (next : BitVec 256 → OracleComp HashSpec α) :
    queries hash (liftM (HashSpec.query input) >>= next) = input :: queries hash (next (hash input)) := rfl

theorem queries_bind {α β : Type} (hash : Hash) (program : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) :
    queries hash (program >>= next) = queries hash program ++ queries hash (next (evalWithAnswerFn hash program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, queries_query_bind, evalWithAnswerFn_bind]
    change input :: queries hash (continuation (hash input) >>= next) =
      (input :: queries hash (continuation (hash input))) ++
        queries hash (next (evalWithAnswerFn hash (continuation (hash input))))
    rw [ih]
    rfl

@[simp] theorem queries_map {α β : Type} (hash : Hash) (f : α → β) (program : OracleComp HashSpec α) :
    queries hash (f <$> program) = queries hash program := by
  rw [map_eq_pure_bind, queries_bind]
  simp

theorem queries_length {α : Type} (hash : Hash) (program : OracleComp HashSpec α) :
    (queries hash program).length = SecurityVerifyCost.calls hash program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rw [queries_query_bind, List.length_cons, SecurityVerifyCost.calls_query_bind, ih]

@[simp] theorem queries_ask (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) :
    queries hash (SecurityReference.ask tag level tree leaf chain step payload) =
      [addressedInput tag level tree leaf chain step payload] := rfl

@[simp] theorem queries_chainHash (hash : Hash) (level tree : Nat) (side : Bool)
    (chain : Chain) (step : Nat) (value : Digest) :
    queries hash (SecurityReference.chainHash level tree side chain step value) =
      [addressedInput 2 level tree (sideNumber side) chain.val step (bytes value)] := by
  simp [SecurityReference.chainHash]

@[simp] theorem queries_compressLeaf (hash : Hash) (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    queries hash (SecurityReference.compressLeaf level tree side values) =
      [addressedInput 3 level tree (sideNumber side) 0 0 ((List.ofFn values).flatMap bytes)] := by
  simp [SecurityReference.compressLeaf]

@[simp] theorem queries_node (hash : Hash) (level tree : Nat) (left right : Digest) :
    queries hash (SecurityReference.node level tree left right) =
      [addressedInput 4 level tree 0 0 0 (bytes left ++ bytes right)] := by
  simp [SecurityReference.node]

theorem mem_sequenceFin {α : Type} (hash : Hash) (n : Nat) (body : Fin n → OracleComp HashSpec α)
    (i : Fin n) (query : Query) (member : query ∈ queries hash (body i)) :
    query ∈ queries hash (SecurityReference.sequenceFin n body) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [SecurityReference.sequenceFin, queries_bind, queries_pure, List.append_nil, List.mem_append]
    refine Fin.cases ?_ (fun j => ?_) i member
    · exact fun h => Or.inl h
    · exact fun h => Or.inr (ih (fun j => body j.succ) j h)

/-- The exact intermediate chain input occurs at every executed suffix offset. -/
theorem mem_walk (hash : Hash) (level tree : Nat) (side : Bool) (chain : Chain)
    (start count offset : Nat) (value : Digest) (within : offset < count) :
    addressedInput 2 level tree (sideNumber side) chain.val (start + offset)
      (bytes (Hypertree.walk (chainHash hash level tree side chain) start offset value)) ∈
    queries hash (SecurityReference.walk (SecurityReference.chainHash level tree side chain) start count value) := by
  induction count generalizing start offset value with
  | zero => omega
  | succ count ih =>
    simp only [SecurityReference.walk, queries_bind, queries_chainHash, SecurityReference.eval_chainHash,
      List.mem_append, List.mem_singleton]
    cases offset with
    | zero => exact Or.inl (by simp [Hypertree.walk])
    | succ offset =>
      right
      simpa only [Hypertree.walk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) offset (chainHash hash level tree side chain start value) (by omega)

theorem mem_recoverLeaf_bottom (hash : Hash) (tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    addressedInput 2 0 tree (sideNumber side) 0 0 (bytes (signature.values 0)) ∈
      queries hash (SecurityVerify.recoverLeaf 0 tree side message signature) := by
  simp [SecurityVerify.recoverLeaf]

theorem mem_recoverLeaf_compress (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (upper : level ≠ 0) :
    addressedInput 3 level tree (sideNumber side) 0 0
      ((List.ofFn fun chain => Hypertree.walk (chainHash hash level tree side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain)).flatMap bytes) ∈
      queries hash (SecurityVerify.recoverLeaf level tree side message signature) := by
  simp only [SecurityVerify.recoverLeaf, upper, if_false, queries_bind,
    SecurityReference.eval_sequenceFin, SecurityReference.eval_walk, SecurityReference.eval_chainHash,
    queries_compressLeaf, List.mem_append, List.mem_singleton, or_true]

theorem mem_recoverLeaf_chain (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (upper : level ≠ 0) (chain : Chain)
    (offset : Nat) (within : offset < 7 - (digit message chain).val) :
    addressedInput 2 level tree (sideNumber side) chain.val ((digit message chain).val + offset)
      (bytes (Hypertree.walk (chainHash hash level tree side chain) (digit message chain).val offset
        (signature.values chain))) ∈ queries hash (SecurityVerify.recoverLeaf level tree side message signature) := by
  simp only [SecurityVerify.recoverLeaf, upper, if_false, queries_bind, List.mem_append]
  exact Or.inl (mem_sequenceFin hash 46 _ chain _ (mem_walk hash level tree side chain _ _ offset _ within))

theorem mem_recoverLayer_leaf (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (query : Query)
    (member : query ∈ queries hash (SecurityVerify.recoverLeaf level tree side message signature)) :
    query ∈ queries hash (SecurityVerify.recoverLayer level tree side message signature) := by
  simp only [SecurityVerify.recoverLayer, queries_bind, List.mem_append]
  exact Or.inl member

theorem mem_recoverLayer_node (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    addressedInput 4 level tree 0 0 0
      (if side then bytes signature.sibling ++ bytes (recoverLeaf hash level tree side message signature)
        else bytes (recoverLeaf hash level tree side message signature) ++ bytes signature.sibling) ∈
      queries hash (SecurityVerify.recoverLayer level tree side message signature) := by
  cases side <;> simp [SecurityVerify.recoverLayer, queries_bind]

/-- The deterministic list is exactly the existing oracle instrumentation,
including its unchanged returned value. Public answers are shared, not resampled. -/
theorem traceHashes_lift {α : Type} (hash : Hash) (answers : QueryImpl World Id)
    (agree : ∀ input, answers (.inr input) = hash input) (program : OracleComp HashSpec α) :
    evalWithAnswerFn answers (SecurityTrace.traceHashes (program.liftComp World)) =
      (evalWithAnswerFn hash program, queries hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    have lifted : (liftM (HashSpec.query input) >>= next).liftComp World =
        (do let answer ← liftM (World.query (.inr input))
            (next answer).liftComp World) := by
      rw [OracleComp.liftComp_bind]
      rfl
    rw [lifted, SecurityTrace.traceHashes_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, queries_query_bind]
    have queried : evalWithAnswerFn answers (liftM (World.query (.inr input))) = hash input := agree input
    rw [queried, ih]
    rfl

end SigGolfCandidate.Hypertree.SecurityVerifyTrace
