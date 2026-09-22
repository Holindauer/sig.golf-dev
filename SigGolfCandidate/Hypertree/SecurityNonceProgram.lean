import SigGolfCandidate.Hypertree.SecurityNonceMonitorCost

namespace SigGolfCandidate.Hypertree.SecurityNonceProgram
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Output-retaining passive nonce syntax. The accumulated success flag and
prereveal count are unavailable to the continuation. -/
inductive Program (α : Type) where
  | pure (value : α)
  | reveal (message : Message) (next : BitVec 256 → Program α)
  | guess (message : Message) (nonce : BitVec 256) (next : Program α)
  | coin (n : Nat) (next : Fin (n + 1) → Program α)
  | bits (next : BitVec 256 → Program α)

def erase {α : Type} : Program α → SecurityNonceMonitor.Strategy
  | .pure _ => .done
  | .reveal message next => .reveal message (fun nonce => erase (next nonce))
  | .guess message nonce next => .guess message nonce (erase next)
  | .coin n next => .coin n (fun value => erase (next value))
  | .bits next => .bits (fun value => erase (next value))

structure Outcome (α : Type) where
  value : α
  bad : Bool
  guesses : Nat

def Outcome.monitor {α : Type} (result : Outcome α) : Bool × Nat := (result.bad, result.guesses)

def addGuess {α : Type} (hidden hit : Bool) (result : Outcome α) : Outcome α :=
  ⟨result.value, (hidden && hit) || result.bad, (if hidden then 1 else 0) + result.guesses⟩

noncomputable def run {α : Type} (table : NonceTable) :
    SecurityNonceMonitor.NonceCache → Program α → ProbComp (Outcome α)
  | _, .pure value => pure ⟨value, false, 0⟩
  | cache, .reveal message next => run table (cache.cacheQuery message (table message)) (next (table message))
  | cache, .guess message nonce next =>
      addGuess (decide (cache message = none)) (decide (table message = nonce)) <$> run table cache next
  | cache, .coin n next => do
      let answer ← $ᵗ Fin (n + 1)
      run table cache (next answer)
  | cache, .bits next => do
      let answer ← $ᵗ BitVec 256
      run table cache (next answer)

/-- The exact joint flag/count projection is the existing nonce monitor; the
relation preserves their correlation, not just their separate marginals. -/
theorem run_projection {α : Type} (table : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (program : Program α) :
    Outcome.monitor <$> run table cache program = SecurityNonceMonitor.play table cache (erase program) := by
  induction program generalizing cache with
  | pure value => rfl
  | reveal message next ih => exact ih (table message) _
  | coin n next ih | bits next ih =>
    simp only [run, erase, SecurityNonceMonitor.play, map_bind, ih]
  | guess message nonce next ih =>
    simp only [run, erase, SecurityNonceMonitor.play, ← ih cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addGuess, Outcome.monitor,
      Bool.decide_and, decide_eq_true_eq]

noncomputable def execute {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    ProbComp (Outcome α) := do
  let table ← $ᵗ NonceTable
  run (SecurityNonceMonitor.complete cache table) cache program

/-- Exact output-forgetting law for eager uniform nonce-table sampling. -/
theorem execute_projection {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    Outcome.monitor <$> execute program cache = SecurityNonceMonitor.experiment (erase program) cache := by
  simp only [execute, SecurityNonceMonitor.experiment, map_bind, run_projection]

/-- Retaining final attacker outputs and charged counters does not change the
passive nonce bound, which charges only the expected prereveal guess count. -/
theorem prob_bad_le_expected {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    Pr[fun result => result.bad = true | execute program cache] ≤
      expectedValue (execute program cache) (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256 := by
  have bound := SecurityNonceMonitor.risk_le_expected (erase program) cache
  rw [← execute_projection, probEvent_map, expectedValue_map] at bound
  exact bound

/-- The sampled counter is exactly the nonce monitor's deferred-sampling cost. -/
theorem expected_guesses {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    expectedValue (execute program cache) (fun result => (result.guesses : ENNReal)) =
      SecurityNonceMonitor.cost cache (erase program) := by
  have same := SecurityNonceMonitor.expected_guesses (erase program) cache
  rw [← execute_projection, expectedValue_map] at same
  exact same

/-- The same joint-output estimate survives an arbitrary randomized initial view. -/
theorem mixed_prob_bad_le_expected {α β : Type} (draw : ProbComp β) (program : β → Program α)
    (cache : β → SecurityNonceMonitor.NonceCache) :
    Pr[fun result => result.bad = true | (do let view ← draw; execute (program view) (cache view))] ≤
      expectedValue (do let view ← draw; execute (program view) (cache view))
        (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256 := by
  rw [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue draw (fun view => expectedValue (execute (program view) (cache view))
        (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256) :=
      expectedValue_mono _ (fun view => prob_bad_le_expected (program view) (cache view))
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

end SigGolfCandidate.Hypertree.SecurityNonceProgram
