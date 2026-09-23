import SigGolfCandidate.Hypertree.SecurityGraphMonitorSign

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorObserve
open SigGolf OracleComp OracleSpec Reference SecurityGraph SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorOracle SecurityGraphChainMonitor
  SecurityGraphFrontier SecurityGraphPublicMonitor SecurityGraphQuery SecurityDerivation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The complete public result of a passive run, forgetting only its tests. -/
noncomputable def observe {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (program : Program α) : ProbComp α := Outcome.value <$> run table cache program

@[simp] theorem observe_done {α : Type} (table : PointTable) (cache : QueryCache PointSpec) (value : α) :
    observe table cache (.done value) = pure value := by simp [observe, run]

@[simp] theorem observe_reveal {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (point : Point) (next : BitVec 256 → Program α) :
    observe table cache (.reveal point next) =
      observe table (cache.cacheQuery point (table point)) (next (table point)) := rfl

@[simp] theorem observe_guess {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (point : Point) (value : Digest) (next : Program α) :
    observe table cache (.guess point value next) = observe table cache next := by
  simp only [observe, run, Functor.map_map, addTest]

@[simp] theorem observe_coin {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (n : Nat) (next : Fin (n+1) → Program α) :
    observe table cache (.coin n next) = (($ᵗ Fin (n+1)) >>= fun value => observe table cache (next value)) := by
  simp only [observe, run, map_bind]

@[simp] theorem observe_bits {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (next : BitVec 256 → Program α) :
    observe table cache (.bits next) = (($ᵗ BitVec 256) >>= fun value => observe table cache (next value)) := by
  simp only [observe, run, map_bind]

@[simp] theorem observe_collision {α : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (target : Digest) (next : BitVec 256 → Program α) :
    observe table cache (.collision target next) = (($ᵗ BitVec 256) >>= fun value => observe table cache (next value)) := by
  simp only [observe, run, map_bind, Functor.map_map, addTest]

@[simp] theorem observe_disclose {α : Type} (table : PointTable) (points : List Point)
    (cache : QueryCache PointSpec) (next : QueryCache PointSpec → Program α) :
    observe table cache (SecurityGraphMonitorOracle.disclose points cache next) =
      observe table (SecurityGraphDisclosure.revealCache table points cache)
        (next (SecurityGraphDisclosure.revealCache table points cache)) := by
  unfold observe
  rw [SecurityGraphMonitorSign.run_disclose]

abbrev Answer := BitVec 256 × QueryCache PointSpec × QueryCache HashSpec

theorem observe_residualStep_bind {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    observe table exposed (SecurityGraphMonitorOracle.residualStep exposed cache query target next) =
      (observe table exposed (SecurityGraphMonitorOracle.residualStep exposed cache query target
        (fun answer opened residual => .done (answer,opened,residual))) >>=
        fun result => observe table result.2.1 (next result.1 result.2.1 result.2.2)) := by
  cases present : cache query with
  | some value => simp only [SecurityGraphMonitorOracle.residualStep, present, observe_done, pure_bind]
  | none =>
    cases known : exposed target <;>
      simp only [SecurityGraphMonitorOracle.residualStep, present, known, observe_bits,
        observe_guess, observe_collision, observe_done, bind_assoc, pure_bind]

theorem observe_knownResidual_bind {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    observe table exposed (SecurityGraphMonitorOracle.knownResidual exposed cache query target next) =
      (observe table exposed (SecurityGraphMonitorOracle.knownResidual exposed cache query target
        (fun answer opened residual => .done (answer,opened,residual))) >>=
        fun result => observe table result.2.1 (next result.1 result.2.1 result.2.2)) := by
  cases present : cache query with
  | some value => simp only [SecurityGraphMonitorOracle.knownResidual, present, observe_done, pure_bind]
  | none =>
    cases target <;>
      simp only [SecurityGraphMonitorOracle.knownResidual, present, observe_bits,
        observe_collision, observe_done, bind_assoc, pure_bind]

theorem observe_chainStep_bind {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    observe table exposed (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) =
      (observe table exposed (SecurityGraphMonitorOracle.chainStep exposed cache address step query
        (fun answer opened residual => .done (answer,opened,residual))) >>=
        fun result => observe table result.2.1 (next result.1 result.2.1 result.2.2)) := by
  unfold SecurityGraphMonitorOracle.chainStep
  cases parsed : payload address step query with
  | none => exact observe_residualStep_bind ..
  | some point =>
    cases known : exposed (predecessor address step) with
    | none => simp only [observe_guess]; exact observe_residualStep_bind ..
    | some value =>
      dsimp only
      split
      · simp only [observe_reveal, observe_done, pure_bind]
      · exact observe_residualStep_bind ..

/-- A public query returns its actual updated caches before its continuation. -/
theorem observe_publicStep_bind {α : Type} (table : PointTable) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    observe table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) =
      (observe table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache query
        (fun answer opened residual => .done (answer,opened,residual))) >>=
        fun result => observe table result.2.1 (next result.1 result.2.1 result.2.2)) := by
  unfold SecurityGraphMonitorOracle.publicStep
  cases located : locate query with
  | none => exact observe_knownResidual_bind ..
  | some position =>
    cases position with
    | chain address step => exact observe_chainStep_bind ..
    | leaf level tree side | node level tree =>
      rw [observe_disclose, observe_disclose]
      dsimp only
      split
      · simp only [observe_done, pure_bind]
      · exact observe_knownResidual_bind ..

theorem observe_indexStep_bind {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache HashSpec → Program α) :
    observe table exposed (SecurityGraphMonitorSign.indexStep cache query next) =
      ((randomOracle (spec := HashSpec) query).run cache >>= fun result =>
        observe table exposed (next result.1 result.2)) := by
  simp only [observe, SecurityGraphMonitorSign.run_indexStep, map_bind]

#print axioms observe_publicStep_bind
end SigGolfCandidate.Hypertree.SecurityGraphMonitorObserve
