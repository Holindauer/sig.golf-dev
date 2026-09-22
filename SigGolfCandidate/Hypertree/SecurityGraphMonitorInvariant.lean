import SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling
import SigGolfCandidate.Hypertree.SecurityGraphAuthorizationDisclosure

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphMonitorCoupling
set_option backward.isDefEq.respectTransparency false
open scoped Classical

/-- Residual cache invariant before the first contact. Every graph-address entry
is both noncanonical and different from that address's fixed truncated target. -/
def ResidualSafe (factors : Factors) (cache : QueryCache HashSpec) : Prop :=
  ∀ query answer, cache query = some answer → ∀ position, locate query = some position →
    query ≠ position.input (privateTable factors) (labels factors) ∧
      truncate answer ≠ truncate (labels factors position)

@[simp] theorem residualSafe_empty (factors : Factors) : ResidualSafe factors ∅ := by
  intro query answer present
  cases present

/-- Repeating an input cannot conceal an old collision: every cached answer was
checked against the same fixed target when it was first inserted. -/
theorem ResidualSafe.chain (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (query : Query) (address : ChainAddress) (step : Fin 7)
    (located : locate query = some (.chain address step)) :
    CacheMiss factors.1 cache query (successor address step) := by
  intro answer present
  exact (safe query answer present (.chain address step) located).2

/-- A fresh noncontact residual answer preserves the invariant for all addresses,
including malformed inputs and addresses other than the updated one. -/
theorem ResidualSafe.cacheQuery (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (query : Query) (answer : BitVec 256)
    (clean : ∀ position, locate query = some position →
      query ≠ position.input (privateTable factors) (labels factors) ∧
        truncate answer ≠ truncate (labels factors position)) :
    ResidualSafe factors (cache.cacheQuery query answer) := by
  intro other value present position located
  by_cases same : other = query
  · subst other
    have values : answer = value := Option.some.inj (by simpa only [QueryCache.cacheQuery_self] using present)
    subst value
    exact clean position located
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other value present position located

/-- Only authorized graph coordinates may be exposed on a contact-free run. -/
def ExposedSafe (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) : Prop :=
  ∀ point value, cache point = some value → Authorized metadata signed point

@[simp] theorem exposedSafe_empty (metadata : MetadataTable) (signed : Finset (BitVec 160)) :
    ExposedSafe metadata signed ∅ := by
  intro point value present
  cases present

theorem ExposedSafe.mono (metadata : MetadataTable) {first second : Finset (BitVec 160)}
    (subset : first ⊆ second) (cache : QueryCache PointSpec) (safe : ExposedSafe metadata first cache) :
    ExposedSafe metadata second cache := by
  intro point value present
  exact authorized_mono metadata subset (safe point value present)

theorem ExposedSafe.cacheQuery (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) (safe : ExposedSafe metadata signed cache)
    (point : Point) (value : BitVec 256) (authorized : Authorized metadata signed point) :
    ExposedSafe metadata signed (cache.cacheQuery point value) := by
  intro other answer present
  by_cases same : other = point
  · subst other; exact authorized
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other answer present

/-- A canonical chain step starting at an authorized predecessor exposes only
another authorized point. This also covers all bottom non-source points. -/
theorem authorized_successor (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (address : ChainAddress) (step : Fin 7)
    (known : Authorized metadata signed (predecessor address step)) :
    Authorized metadata signed (successor address step) := by
  by_cases bottom : address.level.val = 0
  · simp only [Authorized, predecessor, successor, bottom, if_true] at *
    exact Or.inl (by omega)
  · simp only [Authorized, predecessor, successor, bottom, if_false] at *
    exact Nat.le_trans known (by omega)

theorem ExposedSafe.hidden (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) (safe : ExposedSafe metadata signed cache)
    (point : Point) (unauthorized : ¬Authorized metadata signed point) : cache point = none := by
  cases present : cache point with
  | none => rfl
  | some value => exact False.elim (unauthorized (safe point value present))

theorem ExposedSafe.revealCache (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (safe : ExposedSafe metadata signed cache)
    (authorized : ∀ point ∈ points, Authorized metadata signed point) :
    ExposedSafe metadata signed (revealCache table points cache) := by
  induction points generalizing cache with
  | nil => exact safe
  | cons point points ih =>
    exact ih (cache.cacheQuery point (table point))
      (safe.cacheQuery metadata signed cache point (table point) (authorized point (by simp)))
      (fun other member => authorized other (by simp [member]))

end SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant
