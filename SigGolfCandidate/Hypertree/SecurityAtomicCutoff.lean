import SigGolfCandidate.Hypertree.SecurityBudget

namespace SigGolfCandidate.Hypertree.SecurityAtomicCutoff
open SigGolf OracleComp OracleSpec SecurityGameHop SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A fixed charge on every answer history, stronger than equality only for
consistent total hash functions. This permits arbitrary stateful oracle simulation. -/
inductive FixedCost {α : Type} : OracleComp GameWorld α → Nat → Prop where
  | pure (value : α) : FixedCost (pure value) 0
  | query (input : GameWorld.Domain) (next : GameWorld.Range input → OracleComp GameWorld α)
      (cost : Nat) (tails : ∀ answer, FixedCost (next answer) cost) :
      FixedCost (liftM (GameWorld.query input) >>= next) (charge input + cost)

theorem FixedCost.bind {α β : Type} {program : OracleComp GameWorld α} {cost nextCost : Nat}
    (fixed : FixedCost program cost) (next : α → OracleComp GameWorld β)
    (tails : ∀ value, FixedCost (next value) nextCost) : FixedCost (program >>= next) (cost + nextCost) := by
  induction fixed with
  | pure value => simpa only [pure_bind, Nat.zero_add] using tails value
  | query input continuation cost fixed ih =>
    simpa only [bind_assoc, Nat.add_assoc] using
      FixedCost.query input (fun answer => continuation answer >>= next) (cost + nextCost) ih

theorem FixedCost.map {α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (f : α → β) : FixedCost (f <$> program) cost := by
  simpa only [Nat.add_zero, ←map_eq_pure_bind] using fixed.bind (fun value => Pure.pure (f value)) (fun value => FixedCost.pure _)

theorem counted_bind {α β : Type} (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld β) :
    counted (program >>= next) = (do
      let first ← counted program
      let second ← counted (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, counted_query_bind, ih, pure_bind]
    apply bind_congr
    intro answer
    apply bind_congr
    intro first
    apply bind_congr
    intro second
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem FixedCost.counted {α : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) :
    SecurityBudget.counted program = (fun value => (value, cost)) <$> program := by
  induction fixed with
  | pure value => rfl
  | query input next cost fixed ih =>
    rw [counted_query_bind]
    simp only [ih, map_eq_pure_bind, bind_assoc, pure_bind]
    simp only [Nat.add_comm]

/-- Cutoff that retains the unspent budget on successful completion. -/
noncomputable def metered {α : Type} (program : OracleComp GameWorld α) :
    Nat → OracleComp GameWorld (Option (α × Nat)) :=
  OracleComp.construct (fun value budget => pure (some (value, budget)))
    (fun input _ next budget => if charge input ≤ budget then do
      let answer ← liftM (GameWorld.query input)
      next answer (budget - charge input)
    else pure none) program

@[simp] theorem metered_pure {α : Type} (value : α) (budget : Nat) :
    metered (pure value) budget = pure (some (value, budget)) := rfl

theorem metered_query_bind {α : Type} (input : GameWorld.Domain)
    (next : GameWorld.Range input → OracleComp GameWorld α) (budget : Nat) :
    metered (liftM (GameWorld.query input) >>= next) budget =
      if charge input ≤ budget then do
        let answer ← liftM (GameWorld.query input)
        metered (next answer) (budget - charge input)
      else pure none := rfl

/-- Exact bind composition: continuation receives the same output and precisely
the remaining charge, including free coin operations. -/
theorem metered_bind {α β : Type} (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld β) (budget : Nat) :
    metered (program >>= next) budget = (do
      let first ← metered program budget
      match first with
      | none => pure none
      | some (value, remaining) => metered (next value) remaining) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, metered_query_bind]
    split
    · simp only [bind_assoc, ih]
    · simp

theorem cutoff_eq_metered {α : Type} (program : OracleComp GameWorld α) (budget : Nat) :
    cutoff program budget = Option.map Prod.fst <$> metered program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
    rw [cutoff_query_bind, metered_query_bind]
    split
    · simp only [map_bind, ih]
    · rfl

theorem FixedCost.metered_enough {α : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (budget : Nat) (enough : cost ≤ budget) :
    metered program budget = (fun value => some (value, budget - cost)) <$> program := by
  induction fixed generalizing budget with
  | pure value => simp
  | query input next cost fixed ih =>
    rw [metered_query_bind, if_pos (show charge input ≤ budget by omega)]
    rw [map_bind]
    apply bind_congr
    intro answer
    rw [ih answer (budget - charge input) (by omega), Nat.sub_sub]

theorem FixedCost.cutoff_enough {α : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (budget : Nat) (enough : cost ≤ budget) :
    cutoff program budget = some <$> program := by
  rw [cutoff_eq_metered, fixed.metered_enough budget enough]
  simp only [Functor.map_map, Function.comp_def, Option.map_some]

/-- Insufficient-budget execution cannot complete the block, regardless of the
oracle's answers. The prefix may still mutate oracle state before terminal abort. -/
theorem FixedCost.cutoff_insufficient {α : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (budget : Nat) (short : budget < cost)
    (result : Option α) (member : result ∈ support (cutoff program budget)) : result = none := by
  induction fixed generalizing budget with
  | pure value => omega
  | query input next cost fixed ih =>
    rw [cutoff_query_bind] at member
    split at member
    next allowed =>
      rw [mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer (budget - charge input) (by omega) member
    next exhausted => simpa using member

/-- Successful atomic-block composition preserves the complete oracle computation,
so every state mutation and continuation output is retained. -/
theorem FixedCost.bind_enough {α β : Type} {program : OracleComp GameWorld α} {cost : Nat}
    (fixed : FixedCost program cost) (next : α → OracleComp GameWorld β)
    (budget : Nat) (enough : cost ≤ budget) :
    cutoff (program >>= next) budget = (do
      let value ← program
      cutoff (next value) (budget - cost)) := by
  rw [cutoff_eq_metered, metered_bind, fixed.metered_enough budget enough]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro value
  simpa only [map_eq_pure_bind] using (cutoff_eq_metered (next value) (budget - cost)).symm

end SigGolfCandidate.Hypertree.SecurityAtomicCutoff
