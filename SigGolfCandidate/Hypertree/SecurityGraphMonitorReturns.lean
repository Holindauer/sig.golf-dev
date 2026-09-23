import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
  SecurityDerivation SecurityGraph SecurityGraphQuery SecurityGraphChainMonitor SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A structural invariant on every possible public result of a passive program. -/
def AllReturns {α : Type} (property : α → Prop) : Program α → Prop
  | .done value => property value
  | .reveal _ next => ∀ answer, AllReturns property (next answer)
  | .guess _ _ next => AllReturns property next
  | .coin _ next => ∀ answer, AllReturns property (next answer)
  | .bits next => ∀ answer, AllReturns property (next answer)
  | .collision _ next => ∀ answer, AllReturns property (next answer)

theorem run_returns {α : Type} (property : α → Prop) (program : Program α)
    (all : AllReturns property program) (table : PointTable) (cache : QueryCache PointSpec)
    (result : Outcome α) (member : result ∈ support (run table cache program)) : property result.value := by
  induction program generalizing cache result with
  | done value =>
    simp only [run, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact all
  | reveal point next ih => exact ih (table point) (all _) _ _ member
  | guess point value next ih =>
    simp only [run, support_map, Set.mem_image] at member
    obtain ⟨earlier, supported, same⟩ := member
    subst result
    exact ih all cache earlier supported
  | coin n next ih | bits next ih =>
    rw [run, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    exact ih answer (all _) cache result member
  | collision target next ih =>
    simp only [run, mem_support_bind_iff, support_map, Set.mem_image] at member
    obtain ⟨answer, _, earlier, supported, same⟩ := member
    subst result
    exact ih answer (all _) cache earlier supported

theorem disclose_returns {α : Type} (property : α → Prop) (points : List Point)
    (cache : QueryCache PointSpec) (next : QueryCache PointSpec → Program α)
    (all : ∀ opened, AllReturns property (next opened)) :
    AllReturns property (SecurityGraphMonitorOracle.disclose points cache next) := by
  induction points generalizing cache with
  | nil => exact all cache
  | cons point rest ih => exact fun answer => ih (cache.cacheQuery point answer)

theorem residualStep_returns {α : Type} (property : α → Prop)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (all : ∀ answer opened residual, AllReturns property (next answer opened residual)) :
    AllReturns property (SecurityGraphMonitorOracle.residualStep exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.residualStep
  cases cache query with
  | some answer => exact all answer exposed cache
  | none =>
    cases exposed target with
    | some value => exact fun answer => all answer exposed _
    | none => exact fun answer => all answer exposed _

theorem chainStep_returns {α : Type} (property : α → Prop)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7)
    (query : Query) (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (all : ∀ answer opened residual, AllReturns property (next answer opened residual)) :
    AllReturns property (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) := by
  have residual := residualStep_returns property exposed cache query (successor address step) next all
  unfold SecurityGraphMonitorOracle.chainStep
  cases payload address step query with
  | none => exact residual
  | some point =>
    cases exposed (predecessor address step) with
    | none => exact residual
    | some value =>
      dsimp only
      split
      · exact fun answer => all answer _ cache
      · exact residual

theorem knownResidual_returns {α : Type} (property : α → Prop)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (all : ∀ answer opened residual, AllReturns property (next answer opened residual)) :
    AllReturns property (SecurityGraphMonitorOracle.knownResidual exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.knownResidual
  cases cache query with
  | some answer => exact all answer exposed cache
  | none =>
    cases target with
    | some value => exact fun answer => all answer exposed _
    | none => exact fun answer => all answer exposed _

/-- Public-query control flow preserves every continuation invariant, without
conditioning on whether any passive test succeeds. -/
theorem publicStep_returns {α : Type} (property : α → Prop) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (all : ∀ answer opened residual, AllReturns property (next answer opened residual)) :
    AllReturns property (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  unfold SecurityGraphMonitorOracle.publicStep
  cases locate query with
  | none => exact knownResidual_returns property exposed cache query none next all
  | some position =>
    cases position with
    | chain address step => exact chainStep_returns property exposed cache address step query next all
    | leaf level tree side | node level tree =>
      apply disclose_returns
      intro opened
      dsimp only
      split
      · exact all _ _ _
      · exact knownResidual_returns property opened cache query _ next all

end SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
