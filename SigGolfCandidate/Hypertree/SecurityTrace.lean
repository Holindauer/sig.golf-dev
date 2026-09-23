import SigGolfCandidate.Hypertree.SecuritySecretKey

namespace SigGolfCandidate.Hypertree.SecurityTrace
open SigGolf OracleComp OracleSpec SecurityCache SecuritySecretKey
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Record hash inputs only, exactly the resource counted by the security game.
Private uniform queries are deliberately omitted from this log. -/
def prependHash (input : World.Domain) (inputs : List Query) : List Query :=
  match input with
  | .inl _ => inputs
  | .inr input => input :: inputs

noncomputable def traceHashes {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × List Query) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let answer ← liftM (World.query input)
      let result ← next answer
      return (result.1, prependHash input result.2)) computation

@[simp] theorem traceHashes_pure {α : Type} (value : α) :
    traceHashes (pure value) = pure (value, []) := rfl

theorem traceHashes_query_bind {α : Type} (input : World.Domain)
    (next : World.Range input → OracleComp World α) :
    traceHashes (liftM (World.query input) >>= next) = (do
      let answer ← liftM (World.query input)
      let result ← traceHashes (next answer)
      return (result.1, prependHash input result.2)) := rfl

/-- Instrumentation preserves the exact adaptive computation. -/
theorem traceHashes_fst {α : Type} (computation : OracleComp World α) :
    Prod.fst <$> traceHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
    rw [traceHashes_query_bind]
    simp only [map_bind, bind_pure_comp]
    apply bind_congr
    intro answer
    simpa only [Functor.map_map, Function.comp_def] using ih answer

def TraceHits (bad : Query → Prop) (inputs : List Query) : Prop :=
  ∃ input ∈ inputs, bad input

theorem traceHits_prepend (bad : Query → Prop) (input : World.Domain) (inputs : List Query) :
    TraceHits bad (prependHash input inputs) ↔ hashBad bad input ∨ TraceHits bad inputs := by
  cases input <;> simp [TraceHits, prependHash, hashBad]

/-- The stopping probability equals the event in the unmodified adaptive query log. -/
theorem prob_stop_eq_traceHits {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (cache : QueryCache HashSpec) :
    Pr[= none | (simulateQ implementation (stopBefore bad computation)).run' cache] =
      Pr[fun result => TraceHits bad result.2 |
        (simulateQ implementation (traceHashes computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [TraceHits]
  | query_bind input next ih =>
    rw [stopBefore_query_bind, traceHashes_query_bind]
    by_cases hit : hashBad bad input
    · rw [if_pos hit, run'_query_bind]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hit, true_or,
        probEvent_const, NeverFail.probFailure_eq_zero, tsub_zero,
        simulateQ_pure, StateT.run_pure, map_pure, probOutput_pure, ite_true,
        probEvent_bind_of_const, one_mul]
    · rw [if_neg hit, run'_query_bind, run'_query_bind]
      simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro result
      rw [ih result.1 result.2]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hit, false_or]

/-- The bound is on the actual shared-RO trace from the replacement cache. -/
def HashTraceBound {α : Type} (computation : OracleComp World α)
    (cache : QueryCache HashSpec) (limit : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ implementation (traceHashes computation)).run' cache),
    result.2.length ≤ limit

/-- Adaptive hash queries in a secret key-independent replacement world guess the secret key
with probability at most Q/2^128. The computation may use unlimited private coins. -/
theorem prob_stop_secretKey_le {α : Type} (computation : OracleComp World α)
    (cache : QueryCache HashSpec) (limit : Nat) (bounded : HashTraceBound computation cache limit) :
    Pr[= none | sampleSecretKey >>= fun secretKey =>
      (simulateQ implementation (stopBefore (SecretKeyAt · secretKey) computation)).run' cache] ≤
        limit / (2 : ENNReal) ^ 128 := by
  classical
  let trace := (simulateQ implementation (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleSecretKey >>= fun secretKey =>
        (fun result => decide (SecretKeyHitTrace result.2 secretKey)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, prob_stop_eq_traceHits, probOutput_map,
        decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun secretKey => decide (SecretKeyHitTrace result.2 secretKey)) <$> sampleSecretKey] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hr
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (prob_secretKeyHitTrace_le result.2).trans
        (ENNReal.div_le_div (by exact_mod_cast bounded result hr) le_rfl)

/-- Erasing secret key-dependent cache entries from an independent reference world costs
at most Q/2^128. The dependence and query-bound obligations are explicit; this is
one game-hop lemma, not the full hypertree security certificate. -/
theorem prob_secretKey_cache_change_le {α : Type} (computation : OracleComp World α)
    (initial : SecretKey → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (agree : ∀ secretKey, AgreeOutside (SecretKeyAt · secretKey) (initial secretKey) cache)
    (limit : Nat) (bounded : HashTraceBound computation cache limit) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ implementation computation).run' (initial secretKey)] ≤
      Pr[event | (simulateQ implementation computation).run' cache] + limit / (2 : ENNReal) ^ 128 := by
  classical
  let stopped := fun secretKey =>
    (simulateQ implementation (stopBefore (SecretKeyAt · secretKey) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
        (simulateQ implementation computation).run' cache] + Pr[= none | sampleSecretKey >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (prob_cache_change_le (SecretKeyAt · secretKey)
          computation (initial secretKey) cache (agree secretKey) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add
        (le_refl (Pr[event | (simulateQ implementation computation).run' cache]))
        (prob_stop_secretKey_le computation cache limit bounded)

end SigGolfCandidate.Hypertree.SecurityTrace
