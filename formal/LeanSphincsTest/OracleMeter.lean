import LeanSphincs.Benchmark.Target

/-! v0.15 meter boundaries, repeated charging, and the separate raw query budget. -/

open OracleComp OracleSpec LeanSphincs.Benchmark

example : HasVerifyCost (liftM (HashSpec.query [])) 0 :=
  (hasVerifyCost_query_iff [] 0).2 (by decide)

example : HasVerifyCost (liftM (HashSpec.query (List.replicate 64 0))) 1 :=
  (hasVerifyCost_query_iff _ 1).2 (by decide)

example : ¬ HasVerifyCost (liftM (HashSpec.query (List.replicate 65 0))) 1 := by
  rw [hasVerifyCost_query_iff]
  decide

/-- The second identical query costs another unit even with a cached ROM answer. -/
example : HasVerifyCost (do
    let _ ← liftM (HashSpec.query (List.replicate 64 0))
    liftM (HashSpec.query (List.replicate 64 0))) 2 :=
  HasVerifyCost.bind ((hasVerifyCost_query_iff _ 1).2 (by decide))
    (fun _ => (hasVerifyCost_query_iff _ 1).2 (by decide))

private def emptyQuery : OracleComp OracleWorld HashOutput :=
  liftM (OracleWorld.query (.inr []))

/-- Exactly the raw hash predicate used by HasHashQueryBound in the security game. -/
example : emptyQuery.IsQueryBoundP (· matches .inr _) 1 :=
  ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

example : ¬ emptyQuery.IsQueryBoundP (· matches .inr _) 0 := by
  intro h
  exact h.1.elim (fun hnp => hnp rfl) (Nat.not_lt_zero _)
