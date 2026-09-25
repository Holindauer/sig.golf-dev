import SigGolfCandidate.Hypertree.SecurityMonitorIndexContactView
import SigGolfCandidate.Hypertree.SecurityMonitorTranscript
import SigGolfCandidate.Hypertree.SecurityGraphMonitorCompose

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityGraphFactor
  SecurityGraphReference SecurityGraphSigner SecurityGraphExtraction SecurityGraphMonitorCompose
  SecurityMonitorIndexState SecurityMonitorTranscript SecurityMonitorIndexContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The recorded transcript is honest for every total oracle extending the
actual residual cache, and its indices are exactly the authorization history. -/
def Coherent (factors : Factors) (cache : QueryCache HashSpec) (history : History)
    (transcript : Transcript submission.sizes) : Prop :=
  (∀ entry ∈ responses transcript, entry.1 ∈ history.signedMessages) ∧
    ∀ base : Hash, cache.AgreesWithFn base →
      HonestHistory factors base (responses transcript) ∧
      history.signedIndices = Signed factors base (responses transcript)

theorem coherent_empty (factors : Factors) : Coherent factors ∅ (recordKeygen {}) {} := by
  constructor
  · intro entry member; cases member
  · intro base agree
    constructor
    · intro entry member; cases member
    · rfl

theorem Coherent.public {factors : Factors} {cache : QueryCache HashSpec} {history : History}
    {transcript : Transcript submission.sizes} (coherent : Coherent factors cache history transcript)
    (query : Query) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((SecurityGraphOracle.publicOracle
      (privateTable factors) (labels factors) query).run cache)) :
    Coherent factors residual (recordPublic (publicKey factors) history query (cache query).isSome answer) transcript := by
  constructor
  · intro entry present
    rw [public_messages]
    exact coherent.1 entry present
  · intro base agree
    have old := coherent.2 base (query_support_agrees factors query cache (answer,residual) member base agree).1
    exact ⟨old.1, (SecurityMonitorGraphState.public_indices _ _ _ _ _).trans old.2⟩

 theorem random_support_agrees (query : Query) (cache : QueryCache HashSpec)
    (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((randomOracle (spec := HashSpec) query).run cache))
    (base : Hash) (agree : residual.AgreesWithFn base) :
    cache.AgreesWithFn base ∧ base query = answer := by
  cases present : cache query with
  | some value =>
    simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩
    exact ⟨agree, agree present⟩
  | none =>
    simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨value, _, equal⟩ := member
    cases equal
    exact (QueryCache.agreesWithFn_cacheQuery_iff cache query answer base present).mp agree

 theorem upperLayers_length (privateAnswers : SecurityGraphIdeal.PrivateTable) (labels : SecurityGraph.Labels)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    (upperLayers privateAnswers labels count level index hl hi message).length = count := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih => simp only [upperLayers, List.length_cons, ih]

 theorem signature_valid (privateAnswers : SecurityGraphIdeal.PrivateTable) (labels : SecurityGraph.Labels)
    (nonce : Bytes 32) (index : BitVec 160) : (signature privateAnswers labels nonce index).Valid :=
  by
    apply upperLayers_length

 theorem Coherent.sign {factors : Factors} {cache : QueryCache HashSpec} {history : History}
    {transcript : Transcript submission.sizes} (coherent : Coherent factors cache history transcript)
    (message : Message) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((randomOracle (spec := HashSpec)
      (SecurityRandomOracle.indexInput (publicKey factors) message (factors.2.1 message))).run cache)) :
    Coherent factors residual
      (recordSign history message (cache (SecurityRandomOracle.indexInput (publicKey factors) message (factors.2.1 message))).isSome answer)
      (SecurityExperimentAtomic.afterSign transcript message (SecurityExperiment.serialize
        (signature (privateTable factors) (labels factors) (factors.2.1 message) (answer.extractLsb' 0 160)))) := by
  rw [Coherent, responses_after_valid _ _ _ (signature_valid _ _ _ _)]
  constructor
  · intro entry present
    rcases List.mem_cons.mp present with same | old
    · subst entry; exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (coherent.1 entry old)
  · intro base agree
    have replay := random_support_agrees _ cache answer residual member base agree
    have old := coherent.2 base replay.1
    have nonce : privateTable factors (.randomizer message) = factors.2.1 message := rfl
    have indexEq : indexOf (programmed (privateTable factors) (labels factors) base)
        (publicKey factors) message (factors.2.1 message) = answer.extractLsb' 0 160 := by
      rw [index_residual, replay.2]
    constructor
    · intro entry present
      rcases List.mem_cons.mp present with same | present
      · subst entry
        simp only [nonce, indexEq]
      · exact old.1 entry present
    · change insert (answer.extractLsb' 0 160) history.signedIndices = _
      rw [old.2]
      simp only [Signed, List.map_cons, List.toFinset_cons]
      congr 1
      change answer.extractLsb' 0 160 = indexOf _ _ message (factors.2.1 message)
      exact indexEq.symm

end SigGolfCandidate.Hypertree.SecurityMonitorWin
