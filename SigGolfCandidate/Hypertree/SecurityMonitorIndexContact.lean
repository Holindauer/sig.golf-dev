import SigGolfCandidate.Hypertree.SecurityMonitorIndexInvariant
import SigGolfCandidate.Hypertree.SecurityGraphExtraction

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityIndexQuery
  SecurityMonitorIndexState SecurityIndexTrace
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Draw := Query × Entry

def NonceHit (nonces : Message → Bytes 32) (history : History) : Prop :=
  ∃ message, (message, nonces message) ∈ history.nonceGuesses

/-- Ghost provenance retains the input of each fresh H5 draw. It does not add
queries or impose independence on the answers. -/
structure Provenance (nonces : Message → Bytes 32) (pk : PublicKey)
    (cache : QueryCache HashSpec) (history : History) (draws : List Draw) : Prop where
  trace : draws.map Prod.snd = history.indexTrace
  cached : ∀ message nonce answer, cache (indexInput pk message nonce) = some answer →
    ∃ marked, (indexInput pk message nonce, (marked, answer.extractLsb' 0 152)) ∈ draws
  signed : ∀ message ∈ history.signedMessages, NonceHit nonces history ∨
    ∃ answer, cache (indexInput pk message (nonces message)) = some answer ∧
      (indexInput pk message (nonces message), (true, answer.extractLsb' 0 152)) ∈ draws

 theorem provenance_empty (nonces : Message → Bytes 32) (pk : PublicKey) :
    Provenance nonces pk ∅ {} [] := by
  constructor
  · rfl
  · intro message nonce answer present; cases present
  · intro message member; simp at member

/-- Different inputs identify different occurrences, even when their sampled
indices (and hence their projected entries) are equal. -/
theorem conflict_of_draws (draws : List Draw) (first second : Draw)
    (one : first ∈ draws) (two : second ∈ draws) (distinct : first.1 ≠ second.1)
    (same : first.2.2 = second.2.2) (marked : first.2.1 = true ∨ second.2.1 = true) :
    Conflict (draws.map Prod.snd) := by
  induction draws with
  | nil => cases one
  | cons head tail ih =>
    rcases List.mem_cons.mp one with eq | one
    · subst first
      rcases List.mem_cons.mp two with eq | two
      · exact False.elim (distinct (congrArg Prod.fst eq.symm))
      · exact Or.inl ⟨second.2, List.mem_map.mpr ⟨second, two, rfl⟩, same, marked⟩
    · rcases List.mem_cons.mp two with eq | two
      · subst second
        exact Or.inl ⟨first.2, List.mem_map.mpr ⟨first, one, rfl⟩, same.symm, marked.symm⟩
      · exact Or.inr (ih one two)

 theorem index_reuse_contact {nonces : Message → Bytes 32} {pk : PublicKey}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (provenance : Provenance nonces pk cache history draws)
    (hash : Hash) (agree : cache.AgreesWithFn hash)
    (signedMessage message : Message) (nonce : Bytes 32)
    (signed : signedMessage ∈ history.signedMessages)
    (present : cache (indexInput pk message nonce) ≠ none)
    (distinct : indexInput pk signedMessage (nonces signedMessage) ≠ indexInput pk message nonce)
    (same : (hash (indexInput pk signedMessage (nonces signedMessage))).extractLsb' 0 152 =
      (hash (indexInput pk message nonce)).extractLsb' 0 152) :
    Conflict history.indexTrace ∨ NonceHit nonces history := by
  rcases provenance.signed signedMessage signed with hit | ⟨answer, cached, marked⟩
  · exact Or.inr hit
  · obtain ⟨other, otherCached⟩ := Option.ne_none_iff_exists'.mp present
    obtain ⟨flag, logged⟩ := provenance.cached message nonce other otherCached
    left
    rw [← provenance.trace]
    apply conflict_of_draws draws _ _ marked logged distinct
    · simpa only [agree cached, agree otherCached] using same
    · exact Or.inl rfl

theorem extraction_contact (factors : SecurityGraphFactor.Factors) (base : Hash)
    (responses : SecurityForgery.History) (history : History) (cache : QueryCache HashSpec)
    (draws : List Draw)
    (provenance : Provenance (fun m => SecurityGraphFactor.privateTable factors (.randomizer m))
      (SecurityGraphExtraction.publicKey factors) cache history draws)
    (honest : SecurityGraphExtraction.HonestHistory factors base responses)
    (signed : ∀ entry ∈ responses, entry.1 ∈ history.signedMessages)
    (agree : cache.AgreesWithFn (SecurityGraphReference.programmed
      (SecurityGraphFactor.privateTable factors) (SecurityGraphFactor.labels factors) base))
    (message : Message) (signature : SignatureEncoding.Compact)
    (present : cache (indexInput (SecurityGraphExtraction.publicKey factors) message signature.randomizer) ≠ none)
    (reuse : SecurityGraphExtraction.IndexReuse factors base responses message signature) :
    Conflict history.indexTrace ∨
      NonceHit (fun m => SecurityGraphFactor.privateTable factors (.randomizer m)) history := by
  obtain ⟨entry, member, distinct, same⟩ := reuse
  have nonce : entry.2.randomizer = SecurityGraphFactor.privateTable factors (.randomizer entry.1) := by
    rw [honest entry member]
    rfl
  apply index_reuse_contact provenance _ agree entry.1 message signature.randomizer
    (signed entry member) present
  · simpa only [nonce] using distinct
  · simpa only [SecurityGraphExtraction.index, indexOf, query_eq, indexInput, nonce] using same

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorIndexContact.extraction_contact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms extraction_contact
end SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
