import SigGolfCandidate.Hypertree.SecurityGraphPassive

namespace SigGolfCandidate.Hypertree.SecurityGraphChainMonitor
open SigGolf OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphContact
  SecurityGraphFrontier SecurityGraphPassive
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def predecessor (address : ChainAddress) (step : Fin 7) : Point :=
  (address, ⟨step.val, by omega⟩)

def successor (address : ChainAddress) (step : Fin 7) : Point :=
  (address, ⟨step.val + 1, by omega⟩)

theorem predecessor_ne_successor (address : ChainAddress) (step : Fin 7) :
    predecessor address step ≠ successor address step := by
  intro same
  have values := congrArg (fun point : Point => point.2.val) same
  simp only [predecessor, successor] at values
  omega

/-- Payload parsing is independent of every private and graph table. Malformed
inputs do not become guesses merely because they share an address header. -/
noncomputable def payload (address : ChainAddress) (step : Fin 7) (query : Query) : Option Digest :=
  if found : ∃ point, query = chainInput address step point then some found.choose else none

theorem payload_input (address : ChainAddress) (step : Fin 7) (point : Digest) :
    payload address step (chainInput address step point) = some point := by
  unfold payload
  split
  next found =>
    rw [← chainInput_injective address step found.choose_spec]
  next absent => exact False.elim (absent ⟨point, rfl⟩)

theorem payload_some {address : ChainAddress} {step : Fin 7} {query : Query} {point : Digest}
    (parsed : payload address step query = some point) : query = chainInput address step point := by
  unfold payload at parsed
  split at parsed
  next found => cases Option.some.inj parsed; exact found.choose_spec
  next absent => cases parsed

theorem payload_none {address : ChainAddress} {step : Fin 7} {query : Query}
    (parsed : payload address step query = none) (point : Digest) : query ≠ chainInput address step point := by
  intro same
  rw [same, payload_input] at parsed
  cases parsed

/-- A residual cache hit adds no new collision test: its first fresh draw was
already tested against this same, fixed canonical output coordinate. A fresh
answer is tested either against an opened target or passively against a hidden one. -/
noncomputable def residualStep (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) : Strategy :=
  match cache query with
  | some answer => next answer exposed cache
  | none =>
      match exposed target with
      | some known => .collision (truncate known)
          (fun answer => next answer exposed (cache.cacheQuery query answer))
      | none => .bits (fun answer => .guess target (truncate answer)
          (next answer exposed (cache.cacheQuery query answer)))

/-- Operational passive simulation of one actual tag-2 chain query. A known
canonical predecessor opens its successor. An unopened predecessor is only
passively tested, and the continuation receives a residual-oracle answer.
Consequently each public chain call incurs at most two monitor tests. -/
noncomputable def chainStep (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) : Strategy :=
  match payload address step query with
  | none => residualStep exposed cache query (successor address step) next
  | some point =>
      match exposed (predecessor address step) with
      | none => .guess (predecessor address step) point
          (residualStep exposed cache query (successor address step) next)
      | some known =>
          if point = truncate known then
            .reveal (successor address step) (fun answer =>
              next answer (exposed.cacheQuery (successor address step) answer) cache)
          else residualStep exposed cache query (successor address step) next

/-- Before a successful predecessor test, hidden-predecessor handling agrees with
the actual canonical-input comparison. This is the local no-bad relation used by
the global oracle coupling. -/
theorem hidden_miss_noncanonical (table : PointTable) (address : ChainAddress) (step : Fin 7)
    (query : Query) (point : Digest) (parsed : payload address step query = some point)
    (missed : truncate (table (predecessor address step)) ≠ point) :
    query ≠ chainInput address step (truncate (table (predecessor address step))) := by
  intro same
  have equal := chainInput_injective address step ((payload_some parsed).symm.trans same)
  exact missed equal.symm

/-- The known-input branch is exactly the canonical chain-input branch, provided
the exposed cache contains the actual table value. -/
theorem known_matches_canonical (table : PointTable) (address : ChainAddress) (step : Fin 7)
    (query : Query) (point : Digest) (parsed : payload address step query = some point) :
    query = chainInput address step (truncate (table (predecessor address step))) ↔
      point = truncate (table (predecessor address step)) := by
  rw [payload_some parsed]
  exact ⟨fun same => chainInput_injective address step same, congrArg (chainInput address step)⟩

/-- One residual lookup adds at most one passive collision test, and a repeated
lookup adds none. Both known and still-hidden targets are covered. -/
theorem residualStep_within (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) (budget : Nat)
    (bound : ∀ answer exposed cache, Within budget (next answer exposed cache)) :
    Within (budget + 1) (residualStep exposed cache query target next) := by
  unfold residualStep
  split
  next answer present => exact Within.weaken (bound answer exposed cache) (by omega)
  next fresh =>
    split
    next known present => exact Within.collision (fun answer => bound answer _ _)
    next hidden => exact Within.bits (fun answer => Within.guess (bound answer _ _))

/-- At most two monitor tests per actual public chain query, independent of its
address, payload validity, cache status, and previously revealed coordinates. -/
theorem chainStep_within (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Strategy) (budget : Nat)
    (bound : ∀ answer exposed cache, Within budget (next answer exposed cache)) :
    Within (budget + 2) (chainStep exposed cache address step query next) := by
  have residual := residualStep_within exposed cache query (successor address step) next budget bound
  unfold chainStep
  split
  next malformed => exact Within.weaken residual (by omega)
  next point parsed =>
    split
    next hidden => exact Within.guess residual
    next known present =>
      split
      next same =>
        exact Within.weaken (Within.reveal (fun answer => bound answer _ _)) (by omega)
      next different => exact Within.weaken residual (by omega)


end SigGolfCandidate.Hypertree.SecurityGraphChainMonitor
