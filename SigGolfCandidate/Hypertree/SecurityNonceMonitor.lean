import SigGolfCandidate.Hypertree.SecurityGraphFactor
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.Hypertree.SecurityNonceMonitor
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev NonceSpec := Message →ₒ BitVec 256
abbrev NonceCache := QueryCache NonceSpec

/-- Reveals and private coins can affect subsequent choices. Guess success is
only accumulated in a passive flag, never returned to the continuation. -/
inductive Strategy where
  | done
  | reveal (message : Message) (next : BitVec 256 → Strategy)
  | guess (message : Message) (nonce : BitVec 256) (next : Strategy)
  | coin (n : Nat) (next : Fin (n + 1) → Strategy)
  | bits (next : BitVec 256 → Strategy)

def complete (cache : NonceCache) (table : NonceTable) : NonceTable :=
  fun message => (cache message).getD (table message)

theorem complete_update (cache : NonceCache) (table : NonceTable) (message : Message)
    (fresh : cache message = none) (nonce : BitVec 256) :
    complete (cache.cacheQuery message nonce) table = complete cache (Function.update table message nonce) := by
  funext other
  by_cases same : other = message
  · subst other; simp [complete, fresh]
  · simp [complete, same]

theorem cacheQuery_same (cache : NonceCache) (message : Message) (nonce : BitVec 256)
    (present : cache message = some nonce) : cache.cacheQuery message nonce = cache := by
  ext other
  by_cases same : other = message
  · subst other; simp [present]
  · simp [same]

/-- Return both the passive success flag and the number of prereveal guesses.
Already revealed coordinates cost nothing and cannot set the flag. -/
noncomputable def play (table : NonceTable) : NonceCache → Strategy → ProbComp (Bool × Nat)
  | _, .done => pure (false, 0)
  | cache, .reveal message next =>
      play table (cache.cacheQuery message (table message)) (next (table message))
  | cache, .guess message nonce next => do
      let later ← play table cache next
      pure (decide (cache message = none ∧ table message = nonce) || later.1,
        (if cache message = none then 1 else 0) + later.2)
  | cache, .coin n next => do
      let answer ← $ᵗ Fin (n + 1)
      play table cache (next answer)
  | cache, .bits next => do
      let answer ← $ᵗ BitVec 256
      play table cache (next answer)

noncomputable def experiment (strategy : Strategy) (cache : NonceCache) : ProbComp (Bool × Nat) := do
  let table ← $ᵗ NonceTable
  play (complete cache table) cache strategy

/-- Exact expected prereveal work under deferred sampling. No global query cap
is substituted for this quantity. -/
noncomputable def cost : NonceCache → Strategy → ENNReal
  | _, .done => 0
  | cache, .reveal message next => match cache message with
      | some nonce => cost cache (next nonce)
      | none => expectedValue ($ᵗ BitVec 256)
          (fun nonce => cost (cache.cacheQuery message nonce) (next nonce))
  | cache, .guess message _ next => (if cache message = none then 1 else 0) + cost cache next
  | cache, .coin n next => expectedValue ($ᵗ Fin (n + 1)) (fun answer => cost cache (next answer))
  | cache, .bits next => expectedValue ($ᵗ BitVec 256) (fun answer => cost cache (next answer))

theorem uniform_update_bind {α : Type} (message : Message) (next : NonceTable → ProbComp α) :
    𝒮[do
      let nonce ← $ᵗ BitVec 256
      let table ← $ᵗ NonceTable
      next (Function.update table message nonce)] =
      𝒮[do let table ← $ᵗ NonceTable; next table] := by
  calc
    _ = 𝒮[(do let nonce ← $ᵗ BitVec 256; let table ← $ᵗ NonceTable
              pure (Function.update table message nonce)) >>= next] := by
                simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]

theorem uniform_nonce (message : Message) :
    𝒮[(fun table : NonceTable => table message) <$> ($ᵗ NonceTable)] = 𝒮[$ᵗ BitVec 256] := by
  calc
    _ = 𝒮[do
      let nonce ← $ᵗ BitVec 256
      let table ← $ᵗ NonceTable
      pure (Function.update table message nonce message)] := by
        simpa only [map_eq_pure_bind] using
          (uniform_update_bind message (fun table => pure (table message))).symm
    _ = 𝒮[do let nonce ← $ᵗ BitVec 256; pure nonce] := by
      simp only [Function.update_self]
      apply evalSPMF_bind_congr
      intro nonce _
      apply evalSPMF_ext
      intro output
      rw [probOutput_bind_const]
      simp
    _ = _ := by simp

private theorem nonce_density (nonce : BitVec 256) :
    Pr[fun answer : BitVec 256 => answer = nonce | $ᵗ BitVec 256] = 1 / (2 : ENNReal)^256 := by
  simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] using
    SecurityUniform.prob_randomizer_mem ({nonce} : Finset (BitVec 256))

theorem fresh_guess_density (cache : NonceCache) (message : Message) (nonce : BitVec 256)
    (fresh : cache message = none) :
    Pr[fun table : NonceTable => complete cache table message = nonce | $ᵗ NonceTable] =
      1 / (2 : ENNReal)^256 := by
  simp only [complete, fresh, Option.getD_none]
  change Pr[(fun answer : BitVec 256 => answer = nonce) ∘ (fun table : NonceTable => table message) |
    $ᵗ NonceTable] = _
  have same : Pr[fun answer : BitVec 256 => answer = nonce |
      (fun table : NonceTable => table message) <$> ($ᵗ NonceTable)] =
      Pr[fun answer : BitVec 256 => answer = nonce | $ᵗ BitVec 256] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (uniform_nonce message)
  rw [probEvent_map] at same
  exact same.trans (nonce_density nonce)

/-- An unopened message's nonce remains exactly uniform before each passive test. -/
theorem guess_density (cache : NonceCache) (message : Message) (nonce : BitVec 256) :
    Pr[fun table : NonceTable => cache message = none ∧ complete cache table message = nonce |
      $ᵗ NonceTable] = (if cache message = none then (1 : ENNReal) else 0) / (2 : ENNReal)^256 := by
  by_cases fresh : cache message = none
  · simp only [fresh, true_and, if_true]
    exact fresh_guess_density cache message nonce fresh
  · simp only [fresh, false_and, if_false]
    rw [probEvent_False, ENNReal.zero_div]

theorem reveal_fresh (cache : NonceCache) (message : Message) (next : BitVec 256 → Strategy)
    (fresh : cache message = none) :
    𝒮[experiment (.reveal message next) cache] =
      𝒮[do let nonce ← $ᵗ BitVec 256; experiment (next nonce) (cache.cacheQuery message nonce)] := by
  unfold experiment
  simp only [play]
  rw [← uniform_update_bind message]
  simp only [complete_update cache _ message fresh, complete, fresh, Option.getD_none, Function.update_self]

theorem reveal_known (cache : NonceCache) (message : Message) (next : BitVec 256 → Strategy)
    (nonce : BitVec 256) (present : cache message = some nonce) :
    experiment (.reveal message next) cache = experiment (next nonce) cache := by
  simp [experiment, play, complete, present, cacheQuery_same cache message nonce present]

theorem coin_law (cache : NonceCache) (n : Nat) (next : Fin (n + 1) → Strategy) :
    𝒮[experiment (.coin n next) cache] =
      𝒮[do let answer ← $ᵗ Fin (n + 1); experiment (next answer) cache] := by
  unfold experiment
  simp only [play]
  exact evalSPMF_bind_bind_swap _ _ _

theorem bits_law (cache : NonceCache) (next : BitVec 256 → Strategy) :
    𝒮[experiment (.bits next) cache] =
      𝒮[do let answer ← $ᵗ BitVec 256; experiment (next answer) cache] := by
  unfold experiment
  simp only [play]
  exact evalSPMF_bind_bind_swap _ _ _

theorem play_no_failure (strategy : Strategy) (table : NonceTable) (cache : NonceCache) :
    Pr[⊥ | play table cache strategy] = 0 := by
  induction strategy generalizing cache with
  | done => simp [play]
  | reveal message next ih => exact ih (table message) _
  | guess message nonce next ih => simp [play]
  | coin n next ih => simp [play]
  | bits next ih => simp [play]

theorem experiment_no_failure (strategy : Strategy) (cache : NonceCache) :
    Pr[⊥ | experiment strategy cache] = 0 := by
  simp [experiment]

end SigGolfCandidate.Hypertree.SecurityNonceMonitor
