import SigGolfCandidate.Hypertree.SecurityMonitorIndexState

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexInvariant
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityIndexQuery
  SecuritySharedBudget SecuritySeparation SecurityIndexTrace SecurityMonitorIndexState SecurityGraphFactor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Each signed message's deterministic nonce-index input remains in the residual
cache. Thus signing the same message again cannot create a fresh marked draw. -/
def SignedCached (nonces : NonceTable) (pk : PublicKey) (cache : QueryCache HashSpec)
    (history : History) : Prop :=
  ∀ message ∈ history.signedMessages, cache (indexInput pk message (nonces message)) ≠ none

@[simp] theorem signedCached_empty (nonces : NonceTable) (pk : PublicKey) :
    SignedCached nonces pk ∅ {} := by
  simp [SignedCached]

theorem SignedCached.repeated_hit {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (message : Message) (signed : message ∈ history.signedMessages) :
    ∃ answer, cache (indexInput pk message (nonces message)) = some answer :=
  Option.ne_none_iff_exists'.mp (cached message signed)

theorem SignedCached.miss_is_first {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (message : Message) (miss : cache (indexInput pk message (nonces message)) = none) :
    message ∉ history.signedMessages := fun signed => cached message signed miss

theorem SignedCached.fill {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (query : Query) (answer : BitVec 256) :
    SignedCached nonces pk (cache.cacheQuery query answer) history := by
  intro message signed
  by_cases same : indexInput pk message (nonces message) = query
  · rw [same, QueryCache.cacheQuery_self]
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    exact cached message signed

theorem SignedCached.recordPublic {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (query : Query) (hit : Bool) (answer : BitVec 256) :
    SignedCached nonces pk cache (SecurityMonitorIndexState.recordPublic pk history query hit answer) := by
  simpa only [SignedCached, public_messages] using cached

theorem SignedCached.public_fill {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (query : Query) (hit : Bool) (answer : BitVec 256) :
    SignedCached nonces pk (cache.cacheQuery query answer) (SecurityMonitorIndexState.recordPublic pk history query hit answer) :=
  (cached.fill query answer).recordPublic query hit answer

theorem SignedCached.recordSign {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (message : Message) (hit : Bool) (answer : BitVec 256)
    (present : cache (indexInput pk message (nonces message)) ≠ none) :
    SignedCached nonces pk cache (SecurityMonitorIndexState.recordSign history message hit answer) := by
  intro other signed
  rcases Finset.mem_insert.mp signed with same | earlier
  · subst other
    exact present
  · exact cached other earlier

theorem SignedCached.sign_fill {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history)
    (message : Message) (nonce : Bytes 32) (honest : nonce = nonces message)
    (hit : Bool) (answer : BitVec 256) :
    SignedCached nonces pk (cache.cacheQuery (indexInput pk message nonce) answer)
      (SecurityMonitorIndexState.recordSign history message hit answer) := by
  apply (cached.fill _ answer).recordSign message hit answer
  rw [←honest, QueryCache.cacheQuery_self]
  simp

theorem SignedCached.recordKeygen {nonces : NonceTable} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} (cached : SignedCached nonces pk cache history) :
    SignedCached nonces pk cache (SecurityMonitorIndexState.recordKeygen history) := cached

theorem marks_append (first second : List Entry) : marks (first ++ second) = marks first + marks second := by
  induction first with
  | nil => simp [marks]
  | cons entry rest ih => simp only [List.cons_append, marks, ih, Nat.add_assoc]

/-- Bookkeeping charges every public H5 call, while traces contain only fresh
answers and prereveal guesses. Each marked draw requires a newly signed message. -/
def WellCounted (history : History) : Prop :=
  marks history.indexTrace ≤ history.signedMessages.card ∧
  history.indexTrace.length ≤ history.counts.index ∧
  history.nonceGuesses.length ≤ history.counts.index ∧
  history.seedInputs.length = history.counts.seed

@[simp] theorem wellCounted_empty : WellCounted {} := by simp [WellCounted, marks]

theorem WellCounted.recordParsed {history : History} (counted : WellCounted history)
    (query : Query) (parsed : Option (Message × Bytes 32)) (seedEligible hit : Bool) (answer : BitVec 256) :
    WellCounted (SecurityMonitorIndexState.recordParsed history query parsed seedEligible hit answer) := by
  cases parsed with
  | none =>
    cases seedEligible <;> simp only [SecurityMonitorIndexState.recordParsed, Bool.false_eq_true, if_true, if_false,
      WellCounted, List.length_cons] at * <;> omega
  | some pair =>
    rcases pair with ⟨message, nonce⟩
    cases hit <;> by_cases known : message ∈ history.signedMessages <;>
      simp only [SecurityMonitorIndexState.recordParsed, WellCounted, known, if_true, if_false, marks_append, marks, Bool.false_eq_true,
        Nat.zero_add, Nat.add_zero, List.length_append, List.length_cons, List.length_nil] at * <;> omega

theorem WellCounted.recordPublic {history : History} (counted : WellCounted history)
    (pk : PublicKey) (query : Query) (hit : Bool) (answer : BitVec 256) :
    WellCounted (SecurityMonitorIndexState.recordPublic pk history query hit answer) :=
  counted.recordParsed query (parse pk query) (decide (SeedEligible query)) hit answer

theorem WellCounted.recordSign {history : History} (counted : WellCounted history)
    (message : Message) (hit : Bool) (answer : BitVec 256) :
    WellCounted (SecurityMonitorIndexState.recordSign history message hit answer) := by
  cases hit <;> by_cases known : message ∈ history.signedMessages <;>
    simp only [SecurityMonitorIndexState.recordSign, WellCounted, known, decide_true, decide_false, not_true_eq_false,
      not_false_eq_true, if_true, if_false, marks_append, marks, Bool.false_eq_true, Nat.zero_add,
      Nat.add_zero, List.length_append, List.length_cons, List.length_nil,
      Finset.card_insert_of_mem, Finset.card_insert_of_notMem] at * <;> omega

theorem WellCounted.recordKeygen {history : History} (counted : WellCounted history) :
    WellCounted (SecurityMonitorIndexState.recordKeygen history) := counted

/-- The actual lifetime guard supplies the allowance needed by index replay. -/
theorem WellCounted.marks_lifetime {history : History} (counted : WellCounted history)
    (lifetime : history.signedMessages.card ≤ LIFETIME) : marks history.indexTrace ≤ LIFETIME :=
  counted.1.trans lifetime

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorIndexInvariant.WellCounted.recordSign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms WellCounted.recordSign
end SigGolfCandidate.Hypertree.SecurityMonitorIndexInvariant
