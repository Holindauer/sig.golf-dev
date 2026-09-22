import SigGolfCandidate.Hypertree.SecurityDomains

namespace SigGolfCandidate.Hypertree.SecurityGraph
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityPacking SecurityDerivation SecurityDomains

/-- The actual public-hash address fields are byte-sized and occupy disjoint bytes. -/
structure Address where
  tag : Fin 256
  level : Fin 256
  tree : BitVec 192
  leaf : Fin 256
  chain : Fin 256
  step : Fin 256
  deriving DecidableEq

def Address.header (address : Address) : BitVec 64 :=
  BitVec.ofNat 64 (address.tag.val + address.level.val * 2 ^ 8 + address.leaf.val * 2 ^ 16 +
    address.chain.val * 2 ^ 24 + address.step.val * 2 ^ 32)

def Address.input (address : Address) (payload : List Byte) : Query :=
  addressedInput address.tag.val address.level.val address.tree.toNat
    address.leaf.val address.chain.val address.step.val payload

private theorem Address.header_bound (address : Address) :
    address.tag.val + address.level.val * 2 ^ 8 + address.leaf.val * 2 ^ 16 +
      address.chain.val * 2 ^ 24 + address.step.val * 2 ^ 32 < 2 ^ 64 := by
  have := address.tag.isLt
  have := address.level.isLt
  have := address.leaf.isLt
  have := address.chain.isLt
  have := address.step.isLt
  omega

theorem Address.input_eq (address : Address) (payload : List Byte) :
    address.input payload = packed (bytes (n := 8) address.header ++ bytes (n := 24) address.tree ++ payload) := by
  simp [Address.input, addressedInput, Address.header]

/-- Distinct bounded addresses stay distinct for every pair of payloads. -/
theorem Address.eq_of_input_eq {first second : Address} {payload payload' : List Byte}
    (same : first.input payload = second.input payload') : first = second := by
  rw [Address.input_eq, Address.input_eq] at same
  have bytesEq := packed_injective same
  have prefixEq := List.append_inj_left bytesEq (by simp [bytes])
  have headerEq := bytes_injective 8 (List.append_inj_left prefixEq (by simp [bytes]))
  have treeEq := bytes_injective 24 (List.append_inj_right prefixEq (by simp [bytes]))
  have arithmetic := congrArg BitVec.toNat headerEq
  simp only [Address.header, BitVec.toNat_ofNat, Nat.mod_eq_of_lt first.header_bound,
    Nat.mod_eq_of_lt second.header_bound] at arithmetic
  have ht := first.tag.isLt
  have ht' := second.tag.isLt
  have hl := first.level.isLt
  have hl' := second.level.isLt
  have hf := first.leaf.isLt
  have hf' := second.leaf.isLt
  have hc := first.chain.isLt
  have hc' := second.chain.isLt
  have hs := first.step.isLt
  have hs' := second.step.isLt
  have tagEq : first.tag = second.tag := Fin.ext (by omega)
  have levelEq : first.level = second.level := Fin.ext (by omega)
  have leafEq : first.leaf = second.leaf := Fin.ext (by omega)
  have chainEq : first.chain = second.chain := Fin.ext (by omega)
  have stepEq : first.step = second.step := Fin.ext (by omega)
  cases first
  cases second
  cases tagEq
  cases levelEq
  cases treeEq
  cases leafEq
  cases chainEq
  cases stepEq
  rfl

/-- Canonical public graph: seven chain steps, a WOTS leaf compression, and a
binary node compression. Bottom leaves use chain step zero directly. -/
inductive Position where
  | chain (address : ChainAddress) (step : Fin 7)
  | leaf (level : Fin 160) (tree : BitVec 192) (side : Bool)
  | node (level : Fin 160) (tree : BitVec 192)
  deriving DecidableEq

private def levelByte (level : Fin 160) : Fin 256 := ⟨level.val, by omega⟩
private def sideByte (side : Bool) : Fin 256 := ⟨sideNumber side, by cases side <;> decide⟩
private def chainByte (chain : Chain) : Fin 256 := ⟨chain.val, by omega⟩
private def stepByte (step : Fin 7) : Fin 256 := ⟨step.val, by omega⟩

def Position.address : Position → Address
  | .chain address step => ⟨2, levelByte address.level, address.tree, sideByte address.side,
      chainByte address.chain, stepByte step⟩
  | .leaf level tree side => ⟨3, levelByte level, tree, sideByte side, 0, 0⟩
  | .node level tree => ⟨4, levelByte level, tree, 0, 0, 0⟩

private theorem levelByte_injective : Function.Injective levelByte := by
  intro first second same
  exact Fin.ext (congrArg (fun value : Fin 256 => value.val) same)

private theorem chainByte_injective : Function.Injective chainByte := by
  intro first second same
  exact Fin.ext (congrArg (fun value : Fin 256 => value.val) same)

private theorem stepByte_injective : Function.Injective stepByte := by
  intro first second same
  exact Fin.ext (congrArg (fun value : Fin 256 => value.val) same)

private theorem sideByte_injective : Function.Injective sideByte := by
  intro first second same
  cases first <;> cases second <;> simp_all [sideByte, sideNumber]

theorem Position.address_injective : Function.Injective Position.address := by
  intro first second same
  cases first with
  | chain a step =>
    cases second with
    | chain b step' =>
      have level := levelByte_injective (congrArg Address.level same)
      have tree := congrArg Address.tree same
      have side := sideByte_injective (congrArg Address.leaf same)
      have chain := chainByte_injective (congrArg Address.chain same)
      have steps := stepByte_injective (congrArg Address.step same)
      have addresses : a = b := by
        cases a; cases b; cases level; cases tree; cases side; cases chain; rfl
      cases addresses
      cases steps
      rfl
    | leaf level tree side => exact False.elim (by have h := congrArg Address.tag same; cases h)
    | node level tree => exact False.elim (by have h := congrArg Address.tag same; cases h)
  | leaf level tree side =>
    cases second with
    | chain address step => exact False.elim (by have h := congrArg Address.tag same; cases h)
    | leaf level' tree' side' =>
      have levels := levelByte_injective (congrArg Address.level same)
      have trees := congrArg Address.tree same
      have sides := sideByte_injective (congrArg Address.leaf same)
      cases levels
      cases trees
      cases sides
      rfl
    | node level tree => exact False.elim (by have h := congrArg Address.tag same; cases h)
  | node level tree =>
    cases second with
    | chain address step => exact False.elim (by have h := congrArg Address.tag same; cases h)
    | leaf level tree side => exact False.elim (by have h := congrArg Address.tag same; cases h)
    | node level' tree' =>
      have levels := levelByte_injective (congrArg Address.level same)
      have trees := congrArg Address.tree same
      cases levels
      cases trees
      rfl

abbrev Labels := Position → BitVec 256

/-- Inputs are the exact candidate payloads. Canonical outputs can consequently be
sampled independently and planted at one separated input per position. -/
def Position.payload (privateAnswers : Slot → BitVec 256) (labels : Labels) : Position → List Byte
  | .chain address step => bytes (if zero : step.val = 0 then truncate (privateAnswers (.chain address))
      else truncate (labels (.chain address ⟨step.val - 1, by omega⟩)))
  | .leaf level tree side =>
      (List.ofFn (fun chain : Chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)))).flatMap bytes
  | .node level tree =>
      let leaf := fun side => if level.val = 0 then
        truncate (labels (.chain ⟨level, tree, side, 0⟩ 0)) else truncate (labels (.leaf level tree side))
      bytes (leaf false) ++ bytes (leaf true)

def Position.input (privateAnswers : Slot → BitVec 256) (position : Position) (labels : Labels) : Query :=
  position.address.input (position.payload privateAnswers labels)

/-- Every graph vertex has its own H domain for all canonical-label assignments.
This is stronger than distinct inputs within just one honest execution. -/
theorem Position.input_separated (privateAnswers : Slot → BitVec 256)
    (first second : Position) (different : first ≠ second) (before after : Labels) :
    first.input privateAnswers before ≠ second.input privateAnswers after := by
  intro same
  exact different (Position.address_injective (Address.eq_of_input_eq same))

/-- Evaluate a list of actual graph vertices against the public random oracle,
retaining their complete 256-bit outputs. -/
def readGraph (privateAnswers : Slot → BitVec 256) :
    List Position → Labels → OracleComp HashSpec Labels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← HashSpec.query (position.input privateAnswers labels)
      readGraph privateAnswers rest (Function.update labels position answer)

/-- The equivalent independent-label sampler records the exact canonical H inputs
in the real lazy cache. No abstract collision-resistant oracle is substituted. -/
noncomputable def sampleGraph (privateAnswers : Slot → BitVec 256) :
    List Position → Labels → QueryCache HashSpec → ProbComp (Labels × QueryCache HashSpec)
  | [], labels, cache => pure (labels, cache)
  | position :: rest, labels, cache => do
      let answer ← $ᵗ BitVec 256
      sampleGraph privateAnswers rest (Function.update labels position answer)
        (cache.cacheQuery (position.input privateAnswers labels) answer)

/-- Exact, state-preserving lazy sampling of the reference graph. Position
separation makes all unvisited vertices fresh despite adaptively formed payloads. -/
theorem run_readGraph_eq_sampleGraph (privateAnswers : Slot → BitVec 256)
    (positions : List Position) (distinct : positions.Nodup) (labels : Labels)
    (cache : QueryCache HashSpec)
    (fresh : ∀ position ∈ positions, ∀ values, cache (position.input privateAnswers values) = none) :
    (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (readGraph privateAnswers positions labels)).run cache = sampleGraph privateAnswers positions labels cache := by
  induction positions generalizing labels cache with
  | nil => rfl
  | cons position rest ih =>
    obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
    simp only [readGraph, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [randomOracle.run_eq, fresh position (by simp)]
    simp only [bind_assoc, pure_bind, sampleGraph]
    apply bind_congr
    intro answer
    apply ih restDistinct
    intro other member values
    have different : other ≠ position := fun h => notRest (h ▸ member)
    rw [QueryCache.cacheQuery_of_ne _ _ (Position.input_separated privateAnswers other position different values labels)]
    exact fresh other (List.mem_cons_of_mem _ member) values

/-- Empty-cache graph generation is exactly independent sampling plus canonical
cache population, without a freshness assumption left to discharge. -/
theorem run_readGraph_empty (privateAnswers : Slot → BitVec 256)
    (positions : List Position) (distinct : positions.Nodup) (labels : Labels) :
    (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (readGraph privateAnswers positions labels)).run ∅ = sampleGraph privateAnswers positions labels ∅ :=
  run_readGraph_eq_sampleGraph privateAnswers positions distinct labels ∅ (by intros; rfl)

end SigGolfCandidate.Hypertree.SecurityGraph
