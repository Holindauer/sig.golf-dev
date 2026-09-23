import SigGolfCandidate.Hypertree.SecurityGraphMonitorReturns

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
  SecurityDerivation SecurityGraph SecurityGraphQuery SecurityGraphChainMonitor SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A pathwise test ledger: `spent` plus all remaining passive tests is bounded
by the allowance read from the final public result. This retains adaptive costs. -/
def Credit {α : Type} (allowance : α → Nat) : Nat → Program α → Prop
  | spent, .done value => spent ≤ allowance value
  | spent, .reveal _ next => ∀ answer, Credit allowance spent (next answer)
  | spent, .guess _ _ next => Credit allowance (spent + 1) next
  | spent, .coin _ next => ∀ answer, Credit allowance spent (next answer)
  | spent, .bits next => ∀ answer, Credit allowance spent (next answer)
  | spent, .collision _ next => ∀ answer, Credit allowance (spent + 1) (next answer)

theorem Credit.weaken {α : Type} (allowance : α → Nat) (program : Program α)
    {first second : Nat} (less : first ≤ second) (credit : Credit allowance second program) :
    Credit allowance first program := by
  induction program generalizing first second with
  | done value => exact less.trans credit
  | guess point value next ih => exact ih (Nat.add_le_add_right less 1) credit
  | reveal point next ih | coin n next ih | bits next ih =>
    exact fun answer => ih answer less (credit answer)
  | collision target next ih => exact fun answer => ih answer (Nat.add_le_add_right less 1) (credit answer)

/-- The ledger bounds the actual sampled test counter on every supported path,
even after a bad event, since no branch can inspect the passive flag. -/
theorem run_credit {α : Type} (allowance : α → Nat) (program : Program α) (spent : Nat)
    (credit : Credit allowance spent program) (table : PointTable) (cache : QueryCache PointSpec)
    (result : Outcome α) (member : result ∈ support (run table cache program)) :
    spent + result.tests ≤ allowance result.value := by
  induction program generalizing spent cache result with
  | done value =>
    simp only [run, support_pure, Set.mem_singleton_iff] at member
    subst result
    simpa only [Nat.add_zero, Credit] using credit
  | reveal point next ih => exact ih (table point) spent (credit _) _ _ member
  | guess point value next ih =>
    simp only [run, support_map, Set.mem_image] at member
    obtain ⟨earlier, supported, same⟩ := member
    subst result
    have bound := ih (spent + 1) credit cache earlier supported
    change spent + (earlier.tests + 1) ≤ allowance earlier.value
    omega
  | coin n next ih | bits next ih =>
    rw [run, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    exact ih answer spent (credit _) cache result member
  | collision target next ih =>
    simp only [run, mem_support_bind_iff, support_map, Set.mem_image] at member
    obtain ⟨answer, _, earlier, supported, same⟩ := member
    subst result
    have bound := ih answer (spent + 1) (credit answer) cache earlier supported
    change spent + (earlier.tests + 1) ≤ allowance earlier.value
    omega

theorem disclose_credit {α : Type} (allowance : α → Nat) (spent : Nat) (points : List Point)
    (cache : QueryCache PointSpec) (next : QueryCache PointSpec → Program α)
    (credit : ∀ opened, Credit allowance spent (next opened)) :
    Credit allowance spent (SecurityGraphMonitorOracle.disclose points cache next) := by
  induction points generalizing cache with
  | nil => exact credit cache
  | cons point rest ih => exact fun answer => ih (cache.cacheQuery point answer)

theorem residualStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 1) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.residualStep exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.residualStep
  cases cache query with
  | some answer => exact Credit.weaken allowance _ (by omega) (credit answer exposed cache)
  | none =>
    cases exposed target with
    | some value => exact fun answer => credit answer exposed _
    | none => exact fun answer => credit answer exposed _

theorem chainStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7)
    (query : Query) (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 2) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) := by
  have residual := residualStep_credit allowance (spent + 1) exposed cache query (successor address step) next credit
  unfold SecurityGraphMonitorOracle.chainStep
  cases payload address step query with
  | none => exact Credit.weaken allowance _ (by omega) residual
  | some point =>
    cases exposed (predecessor address step) with
    | none => exact residual
    | some value =>
      dsimp only
      split
      · exact fun answer => Credit.weaken allowance _ (by omega) (credit answer _ _)
      · exact Credit.weaken allowance _ (by omega) residual

theorem knownResidual_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 1) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.knownResidual exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.knownResidual
  cases cache query with
  | some answer => exact Credit.weaken allowance _ (by omega) (credit answer exposed cache)
  | none =>
    cases target with
    | some value => exact fun answer => credit answer exposed _
    | none => exact fun answer => Credit.weaken allowance _ (by omega) (credit answer exposed _)

/-- At most two test credits are consumed by each graph-address query. -/
theorem publicStep_credit {α : Type} (allowance : α → Nat) (spent : Nat) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 2) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  have known exposed := knownResidual_credit allowance (spent + 1) exposed cache query
  unfold SecurityGraphMonitorOracle.publicStep
  cases locate query with
  | none => exact Credit.weaken allowance _ (by omega) (known exposed none next credit)
  | some position =>
    cases position with
    | chain address step => exact chainStep_credit allowance spent exposed cache address step query next credit
    | leaf level tree side | node level tree =>
      apply disclose_credit
      intro opened
      dsimp only
      split
      · exact Credit.weaken allowance _ (by omega) (credit _ _ _)
      · exact Credit.weaken allowance _ (by omega) (known opened _ next credit)

/-- Queries outside graph addresses consume no graph-test credits at all. -/
theorem publicStep_outside_credit {α : Type} (allowance : α → Nat) (spent : Nat) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (outside : locate query = none)
    (credit : ∀ answer opened residual, Credit allowance spent (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  simp only [SecurityGraphMonitorOracle.publicStep, outside, SecurityGraphMonitorOracle.knownResidual]
  cases cache query with
  | some answer => exact credit answer exposed cache
  | none => exact fun answer => credit answer exposed _

end SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
