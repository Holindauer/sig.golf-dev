import SigGolfCandidate.Hypertree.SecurityBytecodeCoupling

namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem query_support_agrees (input : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (mem : result ∈ support ((randomOracle (spec := HashSpec) input).run cache))
    (hash : Hash) (agree : result.2.AgreesWithFn hash) :
    cache.AgreesWithFn hash ∧ hash input=result.1 := by
  cases present : cache input with
  | some answer =>
    simp only [randomOracle.run_eq,present,support_pure,Set.mem_singleton_iff] at mem
    subst result
    exact ⟨agree,agree present⟩
  | none =>
    simp only [randomOracle.run_eq,present,bind_pure_comp,support_map,Set.mem_image] at mem
    obtain ⟨answer,_,eq⟩ := mem
    cases eq
    exact (QueryCache.agreesWithFn_cacheQuery_iff cache input answer hash present).mp agree

/-- Every total oracle extending the final cache reproduces the supported output,
not merely some existential oracle. This retains earlier public-key knowledge. -/
theorem runHash_support_agrees {α : Type} (program : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (result : α×QueryCache HashSpec)
    (mem : result ∈ support (runHash program cache)) (hash : Hash)
    (agree : result.2.AgreesWithFn hash) :
    cache.AgreesWithFn hash ∧ evalWithAnswerFn hash program=result.1 := by
  induction program using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    simp only [runHash,simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at mem
    subst result
    exact ⟨agree,rfl⟩
  | query_bind input next ih =>
    have step : runHash (liftM (HashSpec.query input) >>= next) cache =
        (do let answer ← (randomOracle (spec := HashSpec) input).run cache
            runHash (next answer.1) answer.2) := by
      simp only [runHash,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [step,mem_support_bind_iff] at mem
    obtain ⟨answer,queried,tail⟩ := mem
    obtain ⟨earlier,output⟩ := ih answer.1 answer.2 result tail agree
    obtain ⟨original,eq⟩ := query_support_agrees input cache answer queried hash earlier
    refine ⟨original,?_⟩
    simpa only [evalWithAnswerFn_bind,show evalWithAnswerFn hash (liftM (HashSpec.query input))=hash input by rfl,eq] using output

/-- Cache knowledge persists after every hash-only computation. -/
def Knows (cache : QueryCache HashSpec) (fact : Hash → Prop) : Prop :=
  ∀ hash : Hash, cache.AgreesWithFn hash → fact hash

theorem Knows.after {α : Type} {fact : Hash → Prop} (program : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (known : Knows cache fact) (result : α×QueryCache HashSpec)
    (mem : result ∈ support (runHash program cache)) : Knows result.2 fact := by
  intro hash agree
  exact known hash (runHash_support_agrees program cache result mem hash agree).1

/-- A returned oracle-program value is known to every oracle extending its final cache. -/
theorem knows_result {α : Type} (program : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (result : α×QueryCache HashSpec) (mem : result ∈ support (runHash program cache)) :
    Knows result.2 (fun hash => evalWithAnswerFn hash program=result.1) := by
  intro hash agree
  exact (runHash_support_agrees program cache result mem hash agree).2

end SigGolfCandidate.Hypertree.SecurityBytecode
