import SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Stop at the first contact only for coupling. The probability bound is always
proved using the unconditioned passive execution, whose continuation cannot see hits. -/
noncomputable def stopped {α : Type} (table : PointTable) :
    QueryCache PointSpec → Program α → ProbComp (Option α)
  | _, .done value => pure (some value)
  | cache, .reveal point next => stopped table (cache.cacheQuery point (table point)) (next (table point))
  | cache, .guess point value next =>
      if cache point = none ∧ truncate (table point) = value then pure none else stopped table cache next
  | cache, .coin n next => do
      let value ← $ᵗ Fin (n + 1)
      stopped table cache (next value)
  | cache, .bits next => do
      let value ← $ᵗ BitVec 256
      stopped table cache (next value)
  | cache, .collision target next => do
      let value ← $ᵗ BitVec 256
      if truncate value = target then pure none else stopped table cache (next value)

def keep {α : Type} (result : Outcome α) : Option α := if result.bad then none else some result.value

private theorem map_const_spmf {α β : Type} (program : ProbComp α) (value : β) :
    𝒮[(fun _ => value) <$> program] = 𝒮[(pure value : ProbComp β)] := by
  apply evalSPMF_ext
  intro output
  simp only [map_eq_pure_bind, probOutput_bind_const]
  simp

/-- Exact joint observable equivalence between stopping at first contact and
forgetting only bad outcomes of the full passive run. -/
theorem stopped_eq {α : Type} (table : PointTable) (cache : QueryCache PointSpec) (program : Program α) :
    𝒮[stopped table cache program] = 𝒮[keep <$> run table cache program] := by
  induction program generalizing cache with
  | done value => simp [stopped, run, keep]
  | reveal point next ih => exact ih (table point) _
  | guess point value next ih =>
    unfold stopped run
    by_cases hit : cache point = none ∧ truncate (table point) = value
    · simp only [hit, if_true, decide_true, Functor.map_map]
      change 𝒮[pure none] = 𝒮[(fun _ => none) <$> run table cache next]
      exact (map_const_spmf _ _).symm
    · simp only [hit, if_false, decide_false, Functor.map_map]
      change 𝒮[stopped table cache next] = 𝒮[keep <$> run table cache next]
      exact ih cache
  | coin n next ih | bits next ih =>
    simp only [stopped, run, map_bind]
    apply evalSPMF_bind_congr
    intro value _
    exact ih value cache
  | collision target next ih =>
    simp only [stopped, run, map_bind]
    apply evalSPMF_bind_congr
    intro value _
    by_cases hit : truncate value = target
    · simp only [hit, if_true, decide_true, Functor.map_map]
      change 𝒮[pure none] = 𝒮[(fun _ => none) <$> run table cache (next value)]
      exact (map_const_spmf _ _).symm
    · simp only [hit, if_false, decide_false, Functor.map_map]
      change 𝒮[stopped table cache (next value)] = 𝒮[keep <$> run table cache (next value)]
      exact ih value cache

/-- Stopping mass equals the bad-event mass of the unconditioned execution. -/
theorem stopped_none {α : Type} (table : PointTable) (cache : QueryCache PointSpec) (program : Program α) :
    Pr[= none | stopped table cache program] = Pr[fun result => result.bad = true | run table cache program] := by
  rw [probOutput_def, stopped_eq, ← probOutput_def, probOutput_map]
  congr 1
  funext result
  simp [keep]

end SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
