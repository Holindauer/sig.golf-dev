import SigGolfCandidate.Hypertree.SecurityGraphPassiveCost
import SigGolfCandidate.Hypertree.SecurityGraphPublicMonitor

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFrontier
  SecurityGraphPassive SecurityGraphPassiveCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Output-retaining syntax for the passive simulation. Neither a test result nor
its cumulative flag is made available to the next instruction. -/
inductive Program (α : Type) where
  | done (value : α)
  | reveal (point : Point) (next : BitVec 256 → Program α)
  | guess (point : Point) (value : Digest) (next : Program α)
  | coin (n : Nat) (next : Fin (n + 1) → Program α)
  | bits (next : BitVec 256 → Program α)
  | collision (target : Digest) (next : BitVec 256 → Program α)

def erase {α : Type} : Program α → Strategy
  | .done _ => .done
  | .reveal point next => .reveal point (fun value => erase (next value))
  | .guess point value next => .guess point value (erase next)
  | .coin n next => .coin n (fun value => erase (next value))
  | .bits next => .bits (fun value => erase (next value))
  | .collision target next => .collision target (fun value => erase (next value))

structure Outcome (α : Type) where
  value : α
  bad : Bool
  tests : Nat

def addTest {α : Type} (hit : Bool) (result : Outcome α) : Outcome α :=
  ⟨result.value, hit || result.bad, result.tests + 1⟩

noncomputable def run {α : Type} (table : PointTable) :
    QueryCache PointSpec → Program α → ProbComp (Outcome α)
  | _, .done value => pure ⟨value, false, 0⟩
  | cache, .reveal point next => run table (cache.cacheQuery point (table point)) (next (table point))
  | cache, .guess point value next =>
      addTest (decide (cache point = none ∧ truncate (table point) = value)) <$> run table cache next
  | cache, .coin n next => do
      let value ← $ᵗ Fin (n + 1)
      run table cache (next value)
  | cache, .bits next => do
      let value ← $ᵗ BitVec 256
      run table cache (next value)
  | cache, .collision target next => do
      let value ← $ᵗ BitVec 256
      addTest (decide (truncate value = target)) <$> run table cache (next value)

/-- Exact equality, not just a probability inequality: forgetting the public
result and counter recovers the previously bounded passive flag experiment. -/
theorem run_bad {α : Type} (table : PointTable) (cache : QueryCache PointSpec) (program : Program α) :
    Outcome.bad <$> run table cache program = playAll table cache (erase program) := by
  induction program generalizing cache with
  | done value => simp [run, erase, playAll]
  | reveal point next ih => exact ih (table point) _
  | guess point value next ih =>
    simp only [run, erase, playAll, map_eq_pure_bind, bind_assoc]
    rw [← ih cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addTest]
  | coin n next ih | bits next ih =>
    simp only [run, erase, playAll, map_bind]
    exact congrArg (Bind.bind _) (funext (fun value => ih value cache))
  | collision target next ih =>
    simp only [run, erase, playAll, map_bind]
    apply congrArg (Bind.bind _)
    funext value
    rw [← ih value cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addTest]

/-- The counter has the same random path and counts precisely the passive tests. -/
theorem run_tests {α : Type} (table : PointTable) (cache : QueryCache PointSpec) (program : Program α) :
    Outcome.tests <$> run table cache program = tests table cache (erase program) := by
  induction program generalizing cache with
  | done value => simp [run, erase, tests]
  | reveal point next ih => exact ih (table point) _
  | guess point value next ih =>
    simp only [run, erase, tests, ← ih cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addTest]
  | coin n next ih | bits next ih =>
    simp only [run, erase, tests, map_bind]
    exact congrArg (Bind.bind _) (funext (fun value => ih value cache))
  | collision target next ih =>
    simp only [run, erase, tests, map_bind]
    apply congrArg (Bind.bind _)
    funext value
    rw [← ih value cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addTest]

noncomputable def experiment {α : Type} (program : Program α) (cache : QueryCache PointSpec) :
    ProbComp (Outcome α) := do
  let table ← $ᵗ PointTable
  run (complete cache table) cache program

theorem experiment_bad {α : Type} (program : Program α) (cache : QueryCache PointSpec) :
    Outcome.bad <$> experiment program cache = fullExperiment (erase program) cache := by
  simp only [experiment, fullExperiment, map_bind, run_bad]

theorem experiment_tests {α : Type} (program : Program α) (cache : QueryCache PointSpec) :
    Outcome.tests <$> experiment program cache = testExperiment (erase program) cache := by
  simp only [experiment, testExperiment, map_bind, run_tests]

/-- The concrete execution may retain arbitrary outputs and cost annotations.
Its passive contact probability is still bounded by its own expected tests. -/
theorem prob_bad_le_expected {α : Type} (program : Program α) (cache : QueryCache PointSpec) :
    Pr[fun result => result.bad = true | experiment program cache] ≤
      expectedValue (experiment program cache) (fun result => (result.tests : ENNReal)) / 2 ^ 128 := by
  have bound := risk_le_expected (erase program) cache
  rw [risk, ← experiment_bad, probEvent_map, cost, ← experiment_tests, expectedValue_map] at bound
  exact bound

end SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
