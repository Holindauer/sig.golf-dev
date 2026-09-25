import SigGolfCandidate.Hypertree.SecurityAtomicCutoff
import SigGolfCandidate.Hypertree.SecurityIdealSign

namespace SigGolfCandidate.Hypertree.SecurityAtomicCounts
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop SecurityAtomicCutoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Structural query count before embedding a scheme into the charged game.
Every continuation is quantified over every answer, including inconsistent histories. -/
inductive Queries {ι : Type} {spec : OracleSpec ι} {α : Type} : OracleComp spec α → Nat → Prop where
  | pure (value : α) : Queries (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (cost : Nat) (tails : ∀ answer, Queries (next answer) cost) :
      Queries (liftM (spec.query input) >>= next) (1 + cost)

theorem Queries.bind {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {program : OracleComp spec α} {cost nextCost : Nat} (fixed : Queries program cost)
    (next : α → OracleComp spec β) (tails : ∀ value, Queries (next value) nextCost) :
    Queries (program >>= next) (cost + nextCost) := by
  induction fixed with
  | pure value => simpa only [pure_bind, Nat.zero_add] using tails value
  | query input continuation cost fixed ih =>
    simpa only [bind_assoc, Nat.add_assoc] using
      Queries.query input (fun answer => continuation answer >>= next) (cost + nextCost) ih

theorem Queries.map {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {program : OracleComp spec α} {cost : Nat} (fixed : Queries program cost) (f : α → β) :
    Queries (f <$> program) cost := by
  simpa only [Nat.add_zero, ← map_eq_pure_bind] using
    fixed.bind (fun value => Pure.pure (f value)) (fun value => Queries.pure _)

theorem Queries.ask {ι : Type} {spec : OracleSpec ι} (input : spec.Domain) :
    Queries (liftM (spec.query input) : OracleComp spec _) 1 := by
  simpa only [bind_pure, Nat.add_zero] using Queries.query input Pure.pure 0 (fun value => Queries.pure value)

/-- In the scheme's two ports every query has organizer charge one. -/
theorem Queries.fixedCost {α : Type} {program : OracleComp SplitWorld α} {cost : Nat}
    (fixed : Queries program cost) : FixedCost (program.liftComp GameWorld) cost := by
  induction fixed with
  | pure value => exact FixedCost.pure _
  | query input next cost fixed ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change FixedCost (liftM (GameWorld.query (.inr input)) >>= _) (1 + cost)
    exact FixedCost.query (.inr input) _ cost ih

@[simp] theorem ask (tag level tree leaf chain step : Nat) (payload : List Byte) :
    Queries (SecurityReference.ask tag level tree leaf chain step payload) 1 := Queries.ask _

@[simp] theorem chainHash (level tree : Nat) (side : Bool) (chain : Chain) (step : Nat) (value : Digest) :
    Queries (SecurityReference.chainHash level tree side chain step value) 1 :=
  (ask 2 level tree (sideNumber side) chain.val step (bytes value)).map truncate

@[simp] theorem compressLeaf (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    Queries (SecurityReference.compressLeaf level tree side values) 1 :=
  (ask 3 level tree (sideNumber side) 0 0 _).map truncate

@[simp] theorem node (level tree : Nat) (left right : Digest) :
    Queries (SecurityReference.node level tree left right) 1 :=
  (ask 4 level tree 0 0 0 _).map truncate

@[simp] theorem publicCall {α : Type} {program : OracleComp HashSpec α} {cost : Nat}
    (fixed : Queries program cost) : Queries (SecurityIdealKeygen.publicCall program) cost := by
  induction fixed with
  | pure value => exact Queries.pure _
  | query input next cost fixed ih =>
    simp only [SecurityIdealKeygen.publicCall, OracleComp.liftComp_bind, OracleComp.liftComp_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change Queries (liftM (SplitWorld.query (.inr input)) >>= _) (1 + cost)
    exact Queries.query (spec := SplitWorld) (.inr input) _ cost ih

@[simp] theorem secret (address : ChainAddress) : Queries (SecurityIdealKeygen.secret address) 1 := by
  change Queries (truncate <$> (liftM (SplitWorld.query (.inl (.chain address))))) 1
  exact (Queries.ask (spec := SplitWorld) (.inl (.chain address))).map truncate

/-- The number of chain steps is structural, even when each answer is unrelated
to every prior response to the same query. -/
theorem walk {α : Type} (body : Nat → α → OracleComp HashSpec α) (start count : Nat) (value : α)
    (fixed : ∀ step value, Queries (body step value) 1) :
    Queries (SecurityReference.walk body start count value) count := by
  induction count generalizing start value with
  | zero => exact Queries.pure _
  | succ count ih =>
    simpa only [Nat.add_comm, SecurityReference.walk] using
      (fixed start value).bind (fun value' => SecurityReference.walk body (start + 1) count value')
        (fun value' => ih (start + 1) value')

theorem sequenceFin {α : Type} (n cost : Nat) (body : Fin n → OracleComp SplitWorld α)
    (fixed : ∀ i, Queries (body i) cost) : Queries (SecurityIdealKeygen.sequenceFin n body) (n * cost) := by
  induction n with
  | zero => simpa only [Nat.zero_mul, SecurityIdealKeygen.sequenceFin] using (Queries.pure (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
    have tail := ih (fun i => body i.succ) (fun i => fixed i.succ)
    simpa only [SecurityIdealKeygen.sequenceFin, Nat.succ_mul, Nat.add_comm, map_eq_pure_bind]
      using (fixed 0).bind _ (fun head => tail.map (fun tail => (Fin.cases head tail : Fin (n + 1) → α)))

@[simp] theorem endpoint (address : ChainAddress) : Queries (SecurityIdealKeygen.endpoint address) 8 :=
  (secret address).bind _ (fun value => publicCall
    (walk _ 0 7 value (chainHash address.level.val address.tree.toNat address.side address.chain)))

theorem leafRoot (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    Queries (SecurityIdealKeygen.leafRoot level tree side) (if level.val = 0 then 2 else 369) := by
  by_cases bottom : level.val = 0
  · simp only [SecurityIdealKeygen.leafRoot, if_pos bottom]
    exact (secret ⟨level, tree, side, 0⟩).bind _ (fun value => publicCall (chainHash _ _ _ _ _ value))
  · simp only [SecurityIdealKeygen.leafRoot, if_neg bottom]
    exact (sequenceFin 46 8 _ (fun chain => endpoint ⟨level, tree, side, chain⟩)).bind _
      (fun values => publicCall (compressLeaf _ _ _ values))

theorem treeRoot (level : Fin 160) (tree : BitVec 192) :
    Queries (SecurityIdealKeygen.treeRoot level tree) (if level.val = 0 then 5 else 739) := by
  have all := (leafRoot level tree false).bind _ (fun left =>
    (leafRoot level tree true).bind _ (fun right => publicCall (node level.val tree.toNat left right)))
  by_cases bottom : level.val = 0
  · simpa only [SecurityIdealKeygen.treeRoot, if_pos bottom] using all
  · simpa only [SecurityIdealKeygen.treeRoot, if_neg bottom] using all

/-- Actual ideal keygen's charge is fixed on every oracle-answer history. -/
theorem keygen : FixedCost (SecurityIdealKeygen.keygen.liftComp GameWorld) 739 :=
  (treeRoot 159 0).fixedCost

end SigGolfCandidate.Hypertree.SecurityAtomicCounts
