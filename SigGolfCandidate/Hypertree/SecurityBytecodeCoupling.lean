import SigGolfCandidate.Hypertree.SecurityGraphHidden

namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable def runHash {α : Type} (program : OracleComp HashSpec α) (cache : QueryCache HashSpec) :
    ProbComp (α × QueryCache HashSpec) :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) program).run cache

theorem observe_hash_bind {α β : Type} (program : OracleComp HashSpec α)
    (next : α → OracleComp World β) (cache : QueryCache HashSpec) :
    observe (program.liftComp World >>= next) cache =
      (runHash program cache >>= fun result => observe (next result.1) result.2) := by
  simp only [observe,implementation,simulateQ_bind,QueryImpl.simulateQ_add_liftComp_right,
    StateT.run'_eq,StateT.run_bind,map_bind,runHash]

theorem runHash_bind {α β : Type} (program : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) (cache : QueryCache HashSpec) :
    runHash (program >>= next) cache =
      (runHash program cache >>= fun result => runHash (next result.1) result.2) := by
  simp only [runHash,simulateQ_bind,StateT.run_bind]

/-- Two sequential hash computations see one common total oracle on every supported run. -/
theorem joint_support_agrees {α β : Type} (left : OracleComp HashSpec α) (right : OracleComp HashSpec β)
    (cache : QueryCache HashSpec) (result : (α×β)×QueryCache HashSpec)
    (mem : result ∈ support (runHash (do let a←left; let b←right; pure (a,b)) cache)) :
    ∃ hash : Hash, cache.AgreesWithFn hash ∧ evalWithAnswerFn hash left=result.1.1 ∧ evalWithAnswerFn hash right=result.1.2 := by
  obtain ⟨hash,agree,eq⟩ := (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    (do let a←left; let b←right; pure (a,b)) cache result.1).mpr ⟨result.2,mem⟩
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure] at eq
  exact ⟨hash,agree,congrArg Prod.fst eq,congrArg Prod.snd eq⟩

/-- Fixed-oracle equivalence implies contextual lazy-oracle equivalence. Hidden
precomputation is inserted and erased explicitly; the query traces need not match.
The continuation retains its shared oracle cache and arbitrary adaptive private coins. -/
theorem contextual_equivalence_at {α β : Type} (left right : OracleComp HashSpec α)
    (next : α → OracleComp World β) (cache : QueryCache HashSpec)
    (same : ∀ hash : Hash, cache.AgreesWithFn hash → evalWithAnswerFn hash left=evalWithAnswerFn hash right) :
    𝒮[observe (left.liftComp World >>= next) cache] =
      𝒮[observe (right.liftComp World >>= next) cache] := by
  let joint : OracleComp HashSpec (α×α) := do let b←right; let a←left; pure (b,a)
  have unfoldJoint (k : (α×α) → QueryCache HashSpec → ProbComp β) :
      (runHash joint cache >>= fun result => k result.1 result.2) =
      (do let b←runHash right cache; let a←runHash left b.2; k (b.1,a.1) a.2) := by
    simp only [joint,runHash,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,pure_bind,bind_assoc]
  calc
    _ = 𝒮[do let b←runHash right cache; observe (left.liftComp World >>= next) b.2] :=
      (insert_prefix right (left.liftComp World >>= next) cache).symm
    _ = 𝒮[runHash joint cache >>= fun result => observe (next result.1.2) result.2] := by
      rw [unfoldJoint (fun result cache => observe (next result.2) cache)]
      simp only [observe_hash_bind]
    _ = 𝒮[runHash joint cache >>= fun result => observe (next result.1.1) result.2] := by
      apply evalSPMF_bind_congr
      intro result mem
      obtain ⟨hash,agree,hb,ha⟩ := joint_support_agrees right left cache result mem
      have equal : result.1.2=result.1.1 := ha.symm.trans ((same hash agree).trans hb)
      rw [equal]
    _ = 𝒮[do let b←runHash right cache; let a←runHash left b.2; observe (next b.1) a.2] := by
      rw [unfoldJoint (fun result cache => observe (next result.1) cache)]
    _ = 𝒮[runHash right cache >>= fun b => observe (next b.1) b.2] := by
      apply evalSPMF_bind_congr
      intro b _
      exact insert_prefix left (next b.1) b.2
    _ = _ := by rw [observe_hash_bind]

theorem contextual_equivalence {α β : Type} (left right : OracleComp HashSpec α)
    (same : ∀ hash : Hash, evalWithAnswerFn hash left=evalWithAnswerFn hash right)
    (next : α → OracleComp World β) (cache : QueryCache HashSpec) :
    𝒮[observe (left.liftComp World >>= next) cache] =
      𝒮[observe (right.liftComp World >>= next) cache] :=
  contextual_equivalence_at left right next cache (fun hash _ => same hash)

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecode.contextual_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms contextual_equivalence
end SigGolfCandidate.Hypertree.SecurityBytecode
