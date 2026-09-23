import SigGolfCandidate.Hypertree.SecurityMonitorNonceView

namespace SigGolfCandidate.Hypertree.SecurityMonitorNonceView
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphPublicMonitor SecurityGraphMonitorSign
  SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- Nonce coordinates become visible exactly when their message has been signed. -/
def Tracks (cache : SecurityNonceMonitor.NonceCache) (history : History) : Prop :=
  ∀ message, cache message = none ↔ message ∉ history.signedMessages

@[simp] theorem tracks_empty : Tracks ∅ {} := by intro message; simp

theorem Tracks.public {cache : SecurityNonceMonitor.NonceCache} {history : History}
    (tracked : Tracks cache history) (pk : PublicKey) (input : Query) (cached : Bool) (answer : BitVec 256) :
    Tracks cache (recordPublic pk history input cached answer) := by
  intro message
  simpa only [public_messages] using tracked message

theorem Tracks.sign {cache : SecurityNonceMonitor.NonceCache} {history : History}
    (tracked : Tracks cache history) (message : Message) (nonce : BitVec 256) (cached : Bool) (answer : BitVec 256) :
    Tracks (cache.cacheQuery message nonce) (recordSign history message cached answer) := by
  intro other
  by_cases same : other = message
  · subst other
    simp only [QueryCache.cacheQuery_self, recordSign, reduceCtorEq, Finset.mem_insert_self, not_true_eq_false]
  · rw [QueryCache.cacheQuery_of_ne _ _ same, tracked other]
    simp only [recordSign, Finset.mem_insert, same, false_or]

noncomputable def hits (nonces : NonceTable) (history : History) : Bool :=
  history.nonceGuesses.any (fun pair => decide (nonces pair.1 = pair.2))

noncomputable def accumulate {α : Type} (nonces : NonceTable) (history : History) (result : NO α) : NO α :=
  ⟨result.value, hits nonces history || result.bad, history.nonceGuesses.length + result.guesses⟩

noncomputable def annotate {α : Type} (nonces : NonceTable) (result : Result α) : NO (Result α) :=
  ⟨result, hits nonces result.history, result.history.nonceGuesses.length⟩

theorem accumulate_parsed {α : Type} (nonces : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (history : History) (tracked : Tracks cache history) (query : Query)
    (parsed : Option (Message × Bytes 32)) (secretKeyEligible cached : Bool) (answer : BitVec 256) (next : NP α) :
    accumulate nonces history <$> SecurityNonceProgram.run nonces cache (guessParsed history parsed next) =
      accumulate nonces (recordParsed history query parsed secretKeyEligible cached answer) <$>
        SecurityNonceProgram.run nonces cache next := by
  cases parsed with
  | none => cases secretKeyEligible <;> rfl
  | some pair =>
    rcases pair with ⟨message, nonce⟩
    change (accumulate nonces history <$> SecurityNonceProgram.run nonces cache
      (if message ∈ history.signedMessages then next else .guess message nonce next)) = _
    by_cases known : message ∈ history.signedMessages
    · rw [if_pos known]
      simp only [recordParsed, if_pos known]
      rfl
    · rw [if_neg known]
      have hidden := (tracked message).2 known
      simp only [SecurityNonceProgram.run, hidden, decide_true, Functor.map_map]
      congr 1
      funext result
      simp only [accumulate, hits, recordParsed, if_neg known, List.any_cons, List.length_cons,
        SecurityNonceProgram.addGuess, Bool.true_and, ↓reduceIte]
      congr 1
      · simp only [Bool.or_assoc, Bool.or_comm]
      · omega

theorem accumulate_query {α : Type} (nonces : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (history : History) (tracked : Tracks cache history) (pk : PublicKey) (query : Query)
    (cached : Bool) (answer : BitVec 256) (next : NP α) :
    accumulate nonces history <$> SecurityNonceProgram.run nonces cache (guessQuery pk history query next) =
      accumulate nonces (recordPublic pk history query cached answer) <$>
        SecurityNonceProgram.run nonces cache next :=
  accumulate_parsed nonces cache history tracked query (SecurityIndexQuery.parse pk query)
    (decide (SecuritySeparation.SecretKeyEligible query)) cached answer next

@[simp] theorem accumulate_sign {α : Type} (nonces : NonceTable) (history : History)
    (message : Message) (cached : Bool) (answer : BitVec 256) (result : NO α) :
    accumulate nonces (recordSign history message cached answer) result = accumulate nonces history result := rfl

theorem accumulate_parsed_irrel {α : Type} (nonces : NonceTable) (history : History) (query : Query)
    (parsed : Option (Message × Bytes 32)) (eligible cached : Bool) (answer other : BitVec 256) :
    accumulate (α := α) nonces (recordParsed history query parsed eligible cached answer) =
      accumulate nonces (recordParsed history query parsed eligible cached other) := by
  funext result
  cases parsed with
  | none => cases eligible <;> rfl
  | some pair => cases pair; rfl

theorem accumulate_public_irrel {α : Type} (nonces : NonceTable) (history : History) (pk : PublicKey)
    (query : Query) (cached : Bool) (answer other : BitVec 256) :
    accumulate (α := α) nonces (recordPublic pk history query cached answer) =
      accumulate nonces (recordPublic pk history query cached other) :=
  accumulate_parsed_irrel nonces history query (SecurityIndexQuery.parse pk query)
    (decide (SecuritySeparation.SecretKeyEligible query)) cached answer other

/-- Joint flag/counter/output law: the nonce monitor's entire passive observation
is already determined by the common final public history and the fixed table. -/
theorem run_compile {α : Type} (points : PointTable) (nonces : NonceTable)
    (metadata : MetadataTable) (pk : PublicKey) (view : View α) (remaining : Nat)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec) (history : History)
    (nonceCache : SecurityNonceMonitor.NonceCache) (tracked : Tracks nonceCache history) :
    accumulate nonces history <$>
        SecurityNonceProgram.run nonces nonceCache (compile points metadata pk view remaining exposed residual history) =
      annotate nonces <$> SecurityGraphMonitorObserve.observe points exposed
        (SecurityMonitorGraphView.compile nonces metadata pk view remaining exposed residual history) := by
  induction view generalizing remaining exposed residual history nonceCache with
  | done value =>
    simp only [compile, SecurityMonitorGraphView.compile, SecurityNonceProgram.run,
      SecurityGraphMonitorObserve.observe_done, map_pure, accumulate, annotate, Bool.or_false, Nat.add_zero]
  | coin n next ih =>
    rw [compile, SecurityMonitorGraphView.compile, SecurityNonceProgram.run,
      SecurityGraphMonitorObserve.observe_coin, map_bind, map_bind]
    exact bind_congr (fun answer => ih answer _ _ _ _ _ tracked)
  | hash input next ih =>
    cases remaining with
    | zero =>
      simp only [compile, SecurityMonitorGraphView.compile, SecurityNonceProgram.run,
        SecurityGraphMonitorObserve.observe_done, map_pure, accumulate, annotate, Bool.or_false, Nat.add_zero]
    | succ remaining =>
      rw [compile, SecurityMonitorGraphView.compile, accumulate_query nonces nonceCache history tracked pk input _ 0,
        run_liftValue, map_bind, SecurityGraphMonitorObserve.observe_publicStep_bind, map_bind]
      apply bind_congr
      intro result
      rw [accumulate_public_irrel nonces history pk input _ 0 result.1]
      exact ih result.1 _ _ _ _ _ (tracked.public pk input _ result.1)
  | sign signPk message next ih =>
    rw [compile, SecurityMonitorGraphView.compile]
    by_cases allowed : 117508 ≤ remaining
    · rw [if_pos allowed, if_pos allowed, SecurityNonceProgram.run, run_liftValue, map_bind]
      change ((SecurityGraphMonitorObserve.observe points exposed (indexStep residual _ _) >>= _) ) = _
      rw [SecurityGraphMonitorObserve.observe_indexStep_bind,
        SecurityGraphMonitorObserve.observe_indexStep_bind]
      simp only [SecurityGraphMonitorObserve.observe_done, pure_bind, bind_assoc, map_bind]
      apply bind_congr
      intro answer
      rw [run_liftValue, map_bind, SecurityGraphMonitorObserve.observe_disclose]
      change (SecurityGraphMonitorObserve.observe points exposed
        (SecurityGraphMonitorOracle.disclose _ exposed _) >>= _) = _
      rw [SecurityGraphMonitorObserve.observe_disclose, SecurityGraphMonitorObserve.observe_done, pure_bind]
      exact ih _ _ _ _ _ _ (tracked.sign message (nonces message) _ answer.1)
    · rw [if_neg allowed, if_neg allowed]
      simp only [SecurityNonceProgram.run, SecurityGraphMonitorObserve.observe_done,
        map_pure, accumulate, annotate, Bool.or_false, Nat.add_zero]

/-- Starting from no signed messages, the exact nonce hit and counter are the
correct guesses and length of the common final history. -/
theorem run_start {α : Type} (points : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) :
    SecurityNonceProgram.run nonces ∅ (start points metadata pk view budget) =
      annotate nonces <$> SecurityGraphMonitorObserve.observe points ∅
        (SecurityMonitorGraphView.start nonces metadata pk view budget) := by
  rw [start, SecurityMonitorGraphView.start]
  split
  · rw [run_liftValue]
    unfold SecurityGraphMonitorSetup.setup
    change (SecurityGraphMonitorObserve.observe points ∅ (SecurityGraphMonitorOracle.disclose _ ∅ _) >>= _) = _
    rw [SecurityGraphMonitorObserve.observe_disclose, SecurityGraphMonitorObserve.observe_done, pure_bind,
      SecurityGraphMonitorObserve.observe_disclose]
    have tracked : Tracks ∅ (recordKeygen {}) := tracks_empty
    have same := run_compile points nonces metadata pk view (budget - 739)
      (SecurityGraphDisclosure.revealCache points (SecurityGraphMonitorSetup.points metadata) ∅) ∅ (recordKeygen {}) ∅ tracked
    have identity : accumulate (α := Result α) nonces (recordKeygen {}) = id := by
      funext result
      cases result
      simp [accumulate, hits, recordKeygen]
    rw [identity, id_map] at same
    exact same
  · simp only [SecurityNonceProgram.run, SecurityGraphMonitorObserve.observe_done, map_pure, annotate, hits]
    rfl

/-- The eager uniform nonce experiment is precisely the annotated common view. -/
theorem execute_start {α : Type} (points : PointTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) :
    SecurityNonceProgram.execute (start points metadata pk view budget) ∅ = (do
      let nonces ← $ᵗ NonceTable
      annotate nonces <$> SecurityGraphMonitorObserve.observe points ∅
        (SecurityMonitorGraphView.start nonces metadata pk view budget)) := by
  unfold SecurityNonceProgram.execute
  apply bind_congr
  intro nonces
  have empty : SecurityNonceMonitor.complete ∅ nonces = nonces := rfl
  rw [empty, run_start]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorNonceView.run_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_start

end SigGolfCandidate.Hypertree.SecurityMonitorNonceView
