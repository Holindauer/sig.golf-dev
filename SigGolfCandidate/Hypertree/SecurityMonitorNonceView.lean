import SigGolfCandidate.Hypertree.SecurityMonitorNonceLift
import SigGolfCandidate.Hypertree.SecurityGraphMonitorObserve

namespace SigGolfCandidate.Hypertree.SecurityMonitorNonceView
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphPublicMonitor SecurityGraphMonitorSign
  SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

abbrev Result := SecurityMonitorGraphView.Result

/-- Only parsed index probes for a not-yet-signed message are nonce guesses. -/
noncomputable def guessParsed {α : Type} (history : History) (parsed : Option (Message × Bytes 32))
    (next : NP α) : NP α :=
  match parsed with
  | none => next
  | some (message, nonce) =>
      if message ∈ history.signedMessages then next else .guess message nonce next

noncomputable def guessQuery {α : Type} (pk : PublicKey) (history : History) (input : Query)
    (next : NP α) : NP α := guessParsed history (SecurityIndexQuery.parse pk input) next

/-- The nonce projection uses exactly the common simulator's graph macros,
public bookkeeping, budget gates, and adversary continuation. Nonce values are
available to the program only through honest signing disclosures. -/
noncomputable def compile {α : Type} (points : PointTable) (metadata : MetadataTable) (pk : PublicKey) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → NP (Result α)
  | .done value, remaining, exposed, residual, history => .pure ⟨some value, remaining, exposed, residual, history⟩
  | .coin n next, remaining, exposed, residual, history =>
      .coin n (fun answer => compile points metadata pk (next answer) remaining exposed residual history)
  | .hash input next, remaining, exposed, residual, history =>
      match remaining with
      | 0 => .pure ⟨none, 0, exposed, residual, history⟩
      | remaining + 1 => guessQuery pk history input <|
          liftValue points exposed
            (SecurityGraphMonitorOracle.publicStep metadata exposed residual input
              (fun answer opened cache => .done (answer, opened, cache)))
            (fun result => compile points metadata pk (next result.1) remaining result.2.1 result.2.2
              (recordPublic pk history input (residual input).isSome result.1))
  | .sign signPk message next, remaining, exposed, residual, history =>
      if 111596 ≤ remaining then .reveal message (fun nonce =>
        let input := SecurityRandomOracle.indexInput signPk message nonce
        liftValue points exposed (indexStep residual input (fun answer cache => .done (answer, cache)))
          (fun result =>
            let index := result.1.extractLsb' 0 152
            liftValue points exposed (SecurityGraphMonitorOracle.disclose (needed metadata exposed index) exposed .done)
              (fun opened =>
                let factors := viewFactors opened metadata
                let signature := SecurityGraphSigner.signature (privateTable factors) (labels factors) nonce index
                compile points metadata pk (next (SecurityExperiment.serialize signature)) (remaining - 111596)
                  opened result.2 (recordSign history message (residual input).isSome result.1))))
      else .pure ⟨none, remaining, exposed, residual, history⟩

noncomputable def start {α : Type} (points : PointTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) : NP (Result α) :=
  if 739 ≤ budget then
    liftValue points ∅ (SecurityGraphMonitorSetup.setup metadata .done) (fun exposed =>
      compile points metadata pk view (budget - 739) exposed ∅ (recordKeygen {}))
  else .pure ⟨none, budget, ∅, ∅, {}⟩

theorem observe_guessParsed {α : Type} (nonces : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (history : History) (parsed : Option (Message × Bytes 32)) (next : NP α) :
    observe nonces cache (guessParsed history parsed next) = observe nonces cache next := by
  cases parsed with
  | none => rfl
  | some pair =>
    rcases pair with ⟨message, nonce⟩
    change observe nonces cache (if message ∈ history.signedMessages then next else .guess message nonce next) = _
    split
    · rfl
    · simp only [observe, SecurityNonceProgram.run, Functor.map_map]
      rfl

theorem observe_guessQuery {α : Type} (nonces : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (pk : PublicKey) (history : History) (input : Query) (next : NP α) :
    observe nonces cache (guessQuery pk history input next) = observe nonces cache next :=
  observe_guessParsed nonces cache history (SecurityIndexQuery.parse pk input) next

private theorem observe_pure {α : Type} (table : NonceTable) (cache : SecurityNonceMonitor.NonceCache) (value : α) :
    observe table cache (.pure value) = pure value := rfl

private theorem observe_reveal {α : Type} (table : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (message : Message) (next : BitVec 256 → NP α) :
    observe table cache (.reveal message next) =
      observe table (cache.cacheQuery message (table message)) (next (table message)) := rfl

private theorem observe_coin {α : Type} (table : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (n : Nat) (next : Fin (n+1) → NP α) :
    observe table cache (.coin n next) = (($ᵗ Fin (n+1)) >>= fun answer => observe table cache (next answer)) := by
  simp only [observe, SecurityNonceProgram.run, map_bind]

/-- Exact public-output/history marginal of the common simulation, for a fixed
nonce table as well as after its independent uniform sampling. -/
theorem observe_compile {α : Type} (points : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (pk : PublicKey) (view : View α) (remaining : Nat)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec) (history : History)
    (nonceCache : SecurityNonceMonitor.NonceCache) :
    observe nonces nonceCache (compile points metadata pk view remaining exposed residual history) =
      SecurityGraphMonitorObserve.observe points exposed
        (SecurityMonitorGraphView.compile nonces metadata pk view remaining exposed residual history) := by
  induction view generalizing remaining exposed residual history nonceCache with
  | done value => rfl
  | coin n next ih =>
    rw [compile, SecurityMonitorGraphView.compile, observe_coin, SecurityGraphMonitorObserve.observe_coin]
    exact bind_congr (fun answer => ih answer _ _ _ _ _)
  | hash input next ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      rw [compile, SecurityMonitorGraphView.compile, observe_guessQuery, observe_liftValue,
        SecurityGraphMonitorObserve.observe_publicStep_bind]
      apply bind_congr
      intro result
      exact ih result.1 _ _ _ _ _
  | sign signPk message next ih =>
    rw [compile, SecurityMonitorGraphView.compile]
    by_cases allowed : 111596 ≤ remaining
    · rw [if_pos allowed, if_pos allowed, observe_reveal, observe_liftValue]
      change (SecurityGraphMonitorObserve.observe points exposed (indexStep residual _ _) >>= _) = _
      rw [SecurityGraphMonitorObserve.observe_indexStep_bind,
        SecurityGraphMonitorObserve.observe_indexStep_bind]
      simp only [SecurityGraphMonitorObserve.observe_done, pure_bind, bind_assoc]
      apply bind_congr
      intro answer
      rw [observe_liftValue, SecurityGraphMonitorObserve.observe_disclose]
      change (SecurityGraphMonitorObserve.observe points exposed
        (SecurityGraphMonitorOracle.disclose _ exposed _) >>= _) = _
      rw [SecurityGraphMonitorObserve.observe_disclose, SecurityGraphMonitorObserve.observe_done, pure_bind]
      exact ih _ _ _ _ _ _
    · rw [if_neg allowed, if_neg allowed]
      rfl

/-- Key-generation setup uses the same graph disclosure prefix in both projections. -/
theorem observe_start {α : Type} (points : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) (nonceCache : SecurityNonceMonitor.NonceCache) :
    observe nonces nonceCache (start points metadata pk view budget) =
      SecurityGraphMonitorObserve.observe points ∅ (SecurityMonitorGraphView.start nonces metadata pk view budget) := by
  rw [start, SecurityMonitorGraphView.start]
  split
  · rw [observe_liftValue]
    unfold SecurityGraphMonitorSetup.setup
    change (SecurityGraphMonitorObserve.observe points ∅ (SecurityGraphMonitorOracle.disclose _ ∅ _) >>= _) = _
    rw [SecurityGraphMonitorObserve.observe_disclose, SecurityGraphMonitorObserve.observe_done, pure_bind,
      SecurityGraphMonitorObserve.observe_disclose]
    exact observe_compile _ _ _ _ _ _ _ _ _ _
  · rfl

end SigGolfCandidate.Hypertree.SecurityMonitorNonceView
