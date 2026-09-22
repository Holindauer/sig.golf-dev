import SigGolfCandidate.Hypertree.SecurityPath
import SigGolfCandidate.Hypertree.SignatureDecode

namespace SigGolfCandidate.Hypertree.SecurityForgery
open SigGolf Reference SignatureEncoding SecurityPath SecurityRandomOracle SecurityPacking

abbrev History := List (Message × Compact)

def HonestHistory (hash : Hash) (seed : Seed) (history : History) : Prop :=
  ∀ entry ∈ history, entry.2 = SignatureEncoding.signCompact hash seed (Reference.keygen hash seed) entry.1

def index (hash : Hash) (seed : Seed) (message : Message) (signature : Compact) : BitVec 160 :=
  indexOf hash (Reference.keygen hash seed) message signature.randomizer

/-- A different message/randomizer pair reuses an index of an actual signing response. -/
def IndexReuse (hash : Hash) (seed : Seed) (history : History) (message : Message) (signature : Compact) : Prop :=
  ∃ entry ∈ history, index hash seed entry.1 entry.2 = index hash seed message signature ∧
    (entry.1 ≠ message ∨ entry.2.randomizer ≠ signature.randomizer)

/-- The verifier supplies a canonical bottom secret for an index never signed. -/
def NewBottomExposure (hash : Hash) (seed : Seed) (history : History)
    (message : Message) (signature : Compact) : Prop :=
  (∀ entry ∈ history, index hash seed entry.1 entry.2 ≠ index hash seed message signature) ∧
    signature.bottom = secret hash seed 0 ((index hash seed message signature).toNat / 2)
      ((index hash seed message signature).toNat % 2 == 1) 0

def ForgeryPathFault (hash : Hash) (seed : Seed) (message : Message) (signature : Compact) : Prop :=
  PathFault hash seed 0 (index hash seed message signature).toNat 0 signature.toReference.layers

/-- The exact H5 serialization binds both the message and supplied randomizer. -/
theorem indexInput_pair_injective (pk : PublicKey) :
    Function.Injective (fun pair : Message × Bytes 32 => indexInput pk pair.1 pair.2) := by
  intro first second same
  have payload := packed_injective same
  have tails : bytes first.1 ++ bytes first.2 = bytes second.1 ++ bytes second.2 := by
    simp only [indexInput, addressedInput, List.append_assoc] at payload
    exact List.append_cancel_left (List.append_cancel_left (List.append_cancel_left payload))
  exact Prod.ext (bytes_injective 32 (List.append_inj_left tails (by simp)))
    (bytes_injective 32 (List.append_inj_right tails (by simp)))

/-- Reused indices in the extraction are collisions of distinct actual H5 inputs. -/
theorem indexReuse_distinct_inputs (hash : Hash) (seed : Seed) (history : History)
    (message : Message) (signature : Compact) (reuse : IndexReuse hash seed history message signature) :
    ∃ entry ∈ history,
      indexInput (Reference.keygen hash seed) entry.1 entry.2.randomizer ≠
        indexInput (Reference.keygen hash seed) message signature.randomizer ∧
      index hash seed entry.1 entry.2 = index hash seed message signature := by
  obtain ⟨entry, member, same, different⟩ := reuse
  refine ⟨entry, member, ?_, same⟩
  intro equal
  have pair := @indexInput_pair_injective (Reference.keygen hash seed)
    (entry.1, entry.2.randomizer) (message, signature.randomizer) equal
  rcases different with h | h
  · exact h (congrArg Prod.fst pair)
  · exact h (congrArg Prod.snd pair)

/-- Full deterministic strong-forgery extraction for canonical compact signatures.
It covers arbitrary supplied randomizers and maliciously chosen messages. The
three alternatives are explicit obligations for the subsequent ROM probability proof. -/
theorem strong_forgery_extraction (hash : Hash) (seed : Seed) (history : History)
    (honest : HonestHistory hash seed history) (message : Message) (signature : Compact)
    (accepted : Reference.verify hash (Reference.keygen hash seed) message signature.toReference)
    (fresh : (message, signature) ∉ history) :
    ForgeryPathFault hash seed message signature ∨ IndexReuse hash seed history message signature ∨
      NewBottomExposure hash seed history message signature := by
  classical
  by_cases fault : ForgeryPathFault hash seed message signature
  · exact Or.inl fault
  · right
    have canonical := compact_canonical_of_no_fault hash seed message signature accepted fault
    by_cases reused : ∃ entry ∈ history, index hash seed entry.1 entry.2 = index hash seed message signature
    · obtain ⟨entry, member, same⟩ := reused
      left
      refine ⟨entry, member, same, ?_⟩
      by_contra h
      push Not at h
      have rEqual : signature.randomizer = randomizer hash seed message := by
        have signed := honest entry member
        have nonce := congrArg Compact.randomizer signed
        change entry.2.randomizer = randomizer hash seed entry.1 at nonce
        exact h.2.symm.trans (by simpa only [h.1] using nonce)
      have unique := compact_unique_honest_randomizer hash seed message signature accepted rEqual fault
      have record : entry = (message, signature) := by
        apply Prod.ext h.1
        exact (honest entry member).trans (by simpa only [h.1] using unique.symm)
      exact fresh (record ▸ member)
    · right
      refine ⟨?_, ?_⟩
      · intro entry member equal
        exact reused ⟨entry, member, equal⟩
      · exact congrArg Compact.bottom canonical

/-- A fresh-message witness is automatically fresh as a strong compact pair, so
both organizer forgery variants reduce to the same three concrete events. -/
theorem witness_forgery_extraction (hash : Hash) (seed : Seed) (history : History)
    (honest : HonestHistory hash seed history) (message : Message) (signature : Compact)
    (accepted : Reference.verify hash (Reference.keygen hash seed) message signature.toReference)
    (fresh : ∀ entry ∈ history, entry.1 ≠ message) :
    ForgeryPathFault hash seed message signature ∨ IndexReuse hash seed history message signature ∨
      NewBottomExposure hash seed history message signature := by
  apply strong_forgery_extraction hash seed history honest message signature accepted
  intro member
  exact fresh (message, signature) member rfl

end SigGolfCandidate.Hypertree.SecurityForgery
