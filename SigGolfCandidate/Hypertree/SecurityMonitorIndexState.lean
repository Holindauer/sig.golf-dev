import SigGolfCandidate.Hypertree.SecurityIndexQuery
import SigGolfCandidate.Hypertree.SecuritySharedBudget

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexState
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityIndexQuery
  SecuritySharedBudget SecuritySeparation SecurityIndexTrace
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Public bookkeeping; private nonce values are supplied only when signing. -/
structure History where
  signedMessages : Finset Message := ∅
  signedIndices : Finset (BitVec 160) := ∅
  indexTrace : List Entry := []
  nonceGuesses : List (Message × Bytes 32) := []
  secretKeyInputs : List Query := []
  counts : Counts := ⟨0,0,0⟩

/-- Bookkeeping over already classified inputs. Keeping classification opaque
prevents proofs from reducing the existential parser's implementation. -/
noncomputable def recordParsed (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible : Bool) (cached : Bool) (answer : BitVec 256) : History :=
  match parsed with
  | some (message,r) => { history with
      nonceGuesses := if message ∈ history.signedMessages then history.nonceGuesses else (message,r)::history.nonceGuesses
      indexTrace := if cached then history.indexTrace else history.indexTrace ++ [(false,answer.extractLsb' 0 160)]
      counts := {history.counts with index := history.counts.index+1} }
  | none => if secretKeyEligible then { history with
      secretKeyInputs := query::history.secretKeyInputs
      counts := {history.counts with secretKey := history.counts.secretKey+1} }
    else {history with counts := {history.counts with graph := history.counts.graph+1}}

noncomputable def recordPublic (pk : PublicKey) (history : History) (query : Query)
    (cached : Bool) (answer : BitVec 256) : History :=
  recordParsed history query (parse pk query) (decide (SecretKeyEligible query)) cached answer

/-- Honest signing uses one H5 call; its other 117507 calls are charged too. -/
noncomputable def recordSign (history : History) (message : Message) (cached : Bool) (answer : BitVec 256) : History :=
  { history with
    signedMessages := insert message history.signedMessages
    signedIndices := insert (answer.extractLsb' 0 160) history.signedIndices
    indexTrace := if cached then history.indexTrace else
      history.indexTrace ++ [(decide (message ∉ history.signedMessages),answer.extractLsb' 0 160)]
    counts := {history.counts with graph := history.counts.graph+117507, index := history.counts.index+1} }

def recordKeygen (history : History) : History :=
  {history with counts := {history.counts with graph := history.counts.graph+739}}

theorem parsed_total (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible cached : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed secretKeyEligible cached answer).counts.total = history.counts.total+1 := by
  cases parsed with
  | none => cases secretKeyEligible <;> simp only [recordParsed, Bool.false_eq_true, if_false, if_true, Counts.total] <;> omega
  | some pair => rcases pair with ⟨message, nonce⟩; simp only [recordParsed, Counts.total]; omega

theorem public_total (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    (recordPublic pk history query cached answer).counts.total = history.counts.total+1 :=
  parsed_total history query (parse pk query) (decide (SecretKeyEligible query)) cached answer

theorem sign_total (history : History) (message : Message) (cached : Bool) (answer : BitVec 256) :
    (recordSign history message cached answer).counts.total = history.counts.total+117508 := by
  simp only [recordSign, Counts.total]
  omega

theorem keygen_total (history : History) : (recordKeygen history).counts.total = history.counts.total+739 := by
  simp only [recordKeygen, Counts.total]
  omega

theorem parsed_messages (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible cached : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed secretKeyEligible cached answer).signedMessages = history.signedMessages := by
  cases parsed with
  | none => cases secretKeyEligible <;> rfl
  | some pair => cases pair; rfl

@[simp] theorem public_messages (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    (recordPublic pk history query cached answer).signedMessages = history.signedMessages :=
  parsed_messages history query (parse pk query) (decide (SecretKeyEligible query)) cached answer

theorem parsed_guesses_preserved (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible cached : Bool) (answer : BitVec 256)
    (pair : Message × Bytes 32) (member : pair ∈ history.nonceGuesses) :
    pair ∈ (recordParsed history query parsed secretKeyEligible cached answer).nonceGuesses := by
  cases parsed with
  | none => cases secretKeyEligible <;> exact member
  | some other =>
    rcases other with ⟨message, nonce⟩
    change pair ∈ (if message ∈ history.signedMessages then history.nonceGuesses else (message,nonce)::history.nonceGuesses)
    split
    · exact member
    · exact List.mem_cons_of_mem _ member

theorem public_guesses_preserved (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256)
    (pair : Message × Bytes 32) (member : pair ∈ history.nonceGuesses) :
    pair ∈ (recordPublic pk history query cached answer).nonceGuesses :=
  parsed_guesses_preserved history query (parse pk query) (decide (SecretKeyEligible query)) cached answer pair member

/-- Every cached H5 input for an unsigned message is already a logged nonce guess. -/
def NonceCovered (pk : PublicKey) (cache : QueryCache HashSpec) (history : History) : Prop :=
  ∀ message r, cache (indexInput pk message r) ≠ none →
    message ∈ history.signedMessages ∨ (message,r) ∈ history.nonceGuesses

@[simp] theorem nonceCovered_empty (pk : PublicKey) : NonceCovered pk ∅ {} := by
  intro message r present
  exact False.elim (present rfl)

theorem NonceCovered.public_preserved {pk : PublicKey} {cache : QueryCache HashSpec} {history : History}
    (covered : NonceCovered pk cache history) (query : Query) (cached : Bool) (answer : BitVec 256) :
    NonceCovered pk cache (recordPublic pk history query cached answer) := by
  intro message r present
  rcases covered message r present with known | guessed
  · exact Or.inl (by simpa only [public_messages] using known)
  · exact Or.inr (public_guesses_preserved pk history query cached answer _ guessed)

theorem NonceCovered.public_fill {pk : PublicKey} {cache : QueryCache HashSpec} {history : History}
    (covered : NonceCovered pk cache history) (query : Query) (cached : Bool) (answer : BitVec 256) :
    NonceCovered pk (cache.cacheQuery query answer) (recordPublic pk history query cached answer) := by
  intro message r present
  by_cases same : indexInput pk message r = query
  · subst query
    rw [public_messages]
    change message ∈ history.signedMessages ∨ (message,r) ∈
      (recordParsed history (indexInput pk message r) (parse pk (indexInput pk message r))
        (decide (SecretKeyEligible (indexInput pk message r))) cached answer).nonceGuesses
    rw [parse_index]
    by_cases known : message ∈ history.signedMessages
    · exact Or.inl known
    · right
      simp only [recordParsed, if_neg known, List.mem_cons_self]
  · apply covered.public_preserved query cached answer message r
    simpa only [QueryCache.cacheQuery_of_ne _ _ same] using present

theorem NonceCovered.sign_preserved {pk : PublicKey} {cache : QueryCache HashSpec} {history : History}
    (covered : NonceCovered pk cache history) (message : Message) (cached : Bool) (answer : BitVec 256) :
    NonceCovered pk cache (recordSign history message cached answer) := by
  intro other r present
  rcases covered other r present with known | guessed
  · exact Or.inl (Finset.mem_insert_of_mem known)
  · exact Or.inr guessed

theorem NonceCovered.sign_fill {pk : PublicKey} {cache : QueryCache HashSpec} {history : History}
    (covered : NonceCovered pk cache history) (message : Message) (r : Bytes 32) (cached : Bool) (answer : BitVec 256) :
    NonceCovered pk (cache.cacheQuery (indexInput pk message r) answer) (recordSign history message cached answer) := by
  intro other nonce present
  by_cases same : indexInput pk other nonce = indexInput pk message r
  · have pairs := @SecurityForgery.indexInput_pair_injective pk (other, nonce) (message, r) same
    have messages : other = message := congrArg Prod.fst pairs
    exact Or.inl (Finset.mem_insert.mpr (Or.inl messages))
  · apply covered.sign_preserved message cached answer other nonce
    simpa only [QueryCache.cacheQuery_of_ne _ _ same] using present

/-- A first signing cache hit is an exact earlier prereveal nonce prediction. -/
theorem first_sign_hit {pk : PublicKey} {cache : QueryCache HashSpec} {history : History}
    (covered : NonceCovered pk cache history) (message : Message) (r : Bytes 32)
    (fresh : message ∉ history.signedMessages) (present : cache (indexInput pk message r) ≠ none) :
    (message,r) ∈ history.nonceGuesses := (covered message r present).resolve_left fresh

#print axioms first_sign_hit
end SigGolfCandidate.Hypertree.SecurityMonitorIndexState
