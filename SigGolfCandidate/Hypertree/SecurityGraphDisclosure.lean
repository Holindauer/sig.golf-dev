import SigGolfCandidate.Hypertree.SecurityGraphChainMonitor

namespace SigGolfCandidate.Hypertree.SecurityGraphDisclosure
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive

/-- Cache of coordinates deliberately revealed to the passive strategy. -/
def revealCache (table : PointTable) : List Point → QueryCache PointSpec → QueryCache PointSpec
  | [], cache => cache
  | point :: rest, cache => revealCache table rest (cache.cacheQuery point (table point))

/-- Disclose a finite set of known-safe coordinates, without charging guess tests. -/
def disclose : List Point → QueryCache PointSpec → (QueryCache PointSpec → Strategy) → Strategy
  | [], cache, next => next cache
  | point :: rest, cache, next =>
      .reveal point (fun answer => disclose rest (cache.cacheQuery point answer) next)

theorem disclose_within (points : List Point) (cache : QueryCache PointSpec)
    (next : QueryCache PointSpec → Strategy) (budget : Nat)
    (bound : ∀ cache, Within budget (next cache)) : Within budget (disclose points cache next) := by
  induction points generalizing cache with
  | nil => exact bound cache
  | cons point rest ih => exact Within.reveal (fun answer => ih _)

/-- The mathematical cache update is exactly the actual monitor reveal sequence. -/
theorem playAll_disclose (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (next : QueryCache PointSpec → Strategy) :
    playAll table cache (disclose points cache next) =
      playAll table (revealCache table points cache) (next (revealCache table points cache)) := by
  induction points generalizing cache with
  | nil => rfl
  | cons point rest ih => exact ih (cache.cacheQuery point (table point))

/-- Every listed point has its true full value in the resulting exposed cache. -/
theorem revealCache_mem (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (point : Point) (member : point ∈ points) :
    revealCache table points cache point = some (table point) := by
  have preserves (points : List Point) (cache : QueryCache PointSpec)
      (known : cache point = some (table point)) :
      revealCache table points cache point = some (table point) := by
    induction points generalizing cache with
    | nil => exact known
    | cons other rest ih =>
      apply ih
      by_cases same : point = other
      · subst other; simp
      · simpa only [QueryCache.cacheQuery_of_ne _ _ same] using known
  induction points generalizing cache with
  | nil => simp at member
  | cons other rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst other
      exact preserves rest _ (by simp)
    · exact ih _ later

def Agree (table : PointTable) (cache : QueryCache PointSpec) : Prop :=
  ∀ point value, cache point = some value → value = table point

theorem Agree.cacheQuery {table : PointTable} {cache : QueryCache PointSpec}
    (agree : Agree table cache) (point : Point) :
    Agree table (cache.cacheQuery point (table point)) := by
  intro other value present
  by_cases same : other = point
  · subst other
    exact (Option.some.inj ((QueryCache.cacheQuery_self cache point (table point)).symm.trans present)).symm
  · exact agree other value ((QueryCache.cacheQuery_of_ne cache (table point) same).symm.trans present)

theorem Agree.revealCache {table : PointTable} {cache : QueryCache PointSpec}
    (agree : Agree table cache) (points : List Point) : Agree table (revealCache table points cache) := by
  induction points generalizing cache with
  | nil => exact agree
  | cons point rest ih => exact ih (agree.cacheQuery point)

end SigGolfCandidate.Hypertree.SecurityGraphDisclosure
