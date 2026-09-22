import SigGolfCandidate.Hypertree.SecurityGraphMonitorSign
import SigGolfCandidate.Hypertree.SecurityGraphAuthorizationDisclosure

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorSetup
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphFrontier
  SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor SecurityGraphAuthorization
  SecurityGraphMonitorProgram SecurityGraphMonitorSign
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Setup reveals the finite conservative frontier. Its membership depends only
on public metadata, never on any hidden chain-point table value. -/
noncomputable def points (metadata : MetadataTable) : List Point :=
  (Finset.univ.filter (Authorized metadata ∅)).toList

@[simp] theorem mem_points (metadata : MetadataTable) (point : Point) :
    point ∈ points metadata ↔ Authorized metadata ∅ point := by
  simp [points]

theorem points_nodup (metadata : MetadataTable) : (points metadata).Nodup := Finset.nodup_toList _

/-- The initial frontier is executed as actual passive reveals. The continuation
receives the cache built from those reveal answers; it cannot inspect the table. -/
noncomputable def setup {α : Type} (metadata : MetadataTable)
    (next : QueryCache PointSpec → Program α) : Program α :=
  SecurityGraphMonitorOracle.disclose (points metadata) ∅ next

noncomputable def cache (table : PointTable) (metadata : MetadataTable) : QueryCache PointSpec :=
  revealCache table (points metadata) ∅

theorem revealCache_outside (table : PointTable) (points : List Point) (initial : QueryCache PointSpec)
    (point : Point) (absent : point ∉ points) : revealCache table points initial point = initial point := by
  induction points generalizing initial with
  | nil => rfl
  | cons other rest ih =>
    have different : point ≠ other := fun equal => absent (List.mem_cons.mpr (Or.inl equal))
    have later : point ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
    rw [revealCache, ih _ later, QueryCache.cacheQuery_of_ne _ _ different]

/-- Exact cache domain: all initially authorized coordinates and no others. -/
theorem cache_lookup (table : PointTable) (metadata : MetadataTable) (point : Point) :
    cache table metadata point = if Authorized metadata ∅ point then some (table point) else none := by
  by_cases allowed : Authorized metadata ∅ point
  · rw [if_pos allowed]
    exact revealCache_mem table (points metadata) ∅ point ((mem_points metadata point).mpr allowed)
  · rw [if_neg allowed]
    exact revealCache_outside table (points metadata) ∅ point
      (fun member => allowed ((mem_points metadata point).mp member))

theorem cache_agree (table : PointTable) (metadata : MetadataTable) : Agree table (cache table metadata) := by
  intro point value present
  rw [cache_lookup] at present
  split at present
  · exact (Option.some.inj present).symm
  · cases present

theorem cache_covers (table : PointTable) (metadata : MetadataTable) (point : Point)
    (allowed : Authorized metadata ∅ point) : cache table metadata point = some (table point) := by
  rw [cache_lookup, if_pos allowed]

theorem cache_hidden (table : PointTable) (metadata : MetadataTable) (point : Point)
    (hidden : ¬Authorized metadata ∅ point) : cache table metadata point = none := by
  rw [cache_lookup, if_neg hidden]

theorem cache_authorized (table : PointTable) (metadata : MetadataTable) (point : Point) (value : BitVec 256)
    (present : cache table metadata point = some value) : Authorized metadata ∅ point := by
  by_contra hidden
  rw [cache_hidden table metadata point hidden] at present
  cases present

/-- Public metadata reconstruction is available before the first oracle call. -/
theorem cache_publicReady (table : PointTable) (metadata : MetadataTable) :
    PublicReady table (cache table metadata) := by
  intro address step available
  apply cache_covers
  rcases available with bottom | endpoint
  · exact bottom_positive_authorized metadata ∅ address step.succ bottom (by simp)
  · have equal : step.succ = (7 : Fin 8) := Fin.ext (by simp [endpoint])
    rw [equal]
    exact endpoint_authorized metadata ∅ address

/-- Exact operational setup semantics. The continuation's entire output, passive
flag, and test counter are preserved; setup performs no tests of its own. -/
theorem run_setup {α : Type} (table : PointTable) (metadata : MetadataTable)
    (next : QueryCache PointSpec → Program α) :
    run table ∅ (setup metadata next) = run table (cache table metadata) (next (cache table metadata)) :=
  run_disclose table (points metadata) ∅ next

/-- A setup-only program returns the disclosed cache with no bad event or tests. -/
theorem run_setup_done (table : PointTable) (metadata : MetadataTable) :
    run table ∅ (setup metadata (fun opened => .done opened)) =
      pure (⟨cache table metadata, false, 0⟩ : Outcome (QueryCache PointSpec)) := by
  rw [run_setup]
  rfl

theorem run_setup_bad {α : Type} (table : PointTable) (metadata : MetadataTable)
    (next : QueryCache PointSpec → Program α) :
    Outcome.bad <$> run table ∅ (setup metadata next) =
      Outcome.bad <$> run table (cache table metadata) (next (cache table metadata)) := by
  rw [run_setup]

theorem run_setup_tests {α : Type} (table : PointTable) (metadata : MetadataTable)
    (next : QueryCache PointSpec → Program α) :
    Outcome.tests <$> run table ∅ (setup metadata next) =
      Outcome.tests <$> run table (cache table metadata) (next (cache table metadata)) := by
  rw [run_setup]

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphMonitorSetup.cache_publicReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cache_publicReady
/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphMonitorSetup.run_setup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_setup
end SigGolfCandidate.Hypertree.SecurityGraphMonitorSetup
