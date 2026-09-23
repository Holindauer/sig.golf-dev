import SigGolfCandidate.Hypertree.SecurityGraphMonitorCompose
import SigGolfCandidate.Hypertree.SecurityGraphVerifyContact

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorVerify
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram SecurityGraphMonitorChainState SecurityGraphMonitorPublicState
  SecurityGraphMonitorNoContact SecurityGraphMonitorCompose SecurityGraphReference SecurityVerifyTrace
  SecurityGraphTraceContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Result (α : Type) := α × QueryCache PointSpec × QueryCache HashSpec

/-- Compile the actual hash-only verifier computation, preserving its output and
both resulting caches. Every query is handled by the concrete passive oracle. -/
noncomputable def compile {α : Type} (metadata : MetadataTable) (program : OracleComp HashSpec α) :
    QueryCache PointSpec → QueryCache HashSpec → Program (Result α) :=
  OracleComp.construct
    (fun value exposed residual => .done (value, exposed, residual))
    (fun query _ next exposed residual =>
      SecurityGraphMonitorOracle.publicStep metadata exposed residual query
        (fun answer opened cache => next answer opened cache)) program

@[simp] theorem compile_pure {α : Type} (metadata : MetadataTable) (value : α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) :
    compile metadata (pure value) exposed cache = .done (value, exposed, cache) := rfl

theorem compile_query {α : Type} (metadata : MetadataTable) (query : Query)
    (next : BitVec 256 → OracleComp HashSpec α) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) :
    compile metadata (liftM (HashSpec.query query) >>= next) exposed cache =
      SecurityGraphMonitorOracle.publicStep metadata exposed cache query
        (fun answer opened residual => compile metadata (next answer) opened residual) := rfl

/-- Every normally completed monitored computation is the genuine verifier run
under every total residual oracle extending its final cache. Its complete actual
query log contains no extracted contact, and all invariants persist. -/
theorem completed {α : Type} (factors : Factors) (signed : Finset (BitVec 152))
    (program : OracleComp HashSpec α) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe factors signed exposed cache) (result : Result α)
    (member : some result ∈ support (stopped factors.1 exposed (compile factors.2.2 program exposed cache)))
    (base : Hash) (agree : result.2.2.AgreesWithFn base) :
    cache.AgreesWithFn base ∧
      evalWithAnswerFn (programmed (privateTable factors) (labels factors) base) program = result.1 ∧
      Safe factors signed result.2.1 result.2.2 ∧
      ∀ query ∈ queries (programmed (privateTable factors) (labels factors) base) program,
        ¬Contact factors signed (programmed (privateTable factors) (labels factors) base) query := by
  induction program using OracleComp.inductionOn generalizing exposed cache result with
  | pure value =>
    simp only [compile_pure, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact ⟨agree, rfl, initial, by simp⟩
  | query_bind query next ih =>
    rw [compile_query, stopped_public_bind factors signed exposed cache initial] at member
    rw [mem_support_bind_iff] at member
    obtain ⟨read, queried, tail⟩ := member
    cases read with
    | none => simp only [continueWith, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
    | some answer =>
      have nextSafe := public_read_safe factors signed exposed cache initial query answer queried
      have later := ih answer.1 answer.2.1 answer.2.2 nextSafe result tail agree
      have spec := read_spec factors signed exposed cache initial query answer queried
      have replay := query_support_agrees factors query cache (answer.1, answer.2.2) spec.2.2.2 base later.1
      refine ⟨replay.1, ?_, later.2.2.1, ?_⟩
      · change evalWithAnswerFn (programmed (privateTable factors) (labels factors) base)
          (next (programmed (privateTable factors) (labels factors) base query)) = result.1
        rw [replay.2]
        exact later.2.1
      · rw [queries_query_bind, replay.2]
        intro other present
        rcases List.mem_cons.mp present with same | rest
        · subst other
          exact read_no_contact factors signed exposed cache initial query answer _ replay.2 queried
        · exact later.2.2.2 other rest

/-- A fresh accepted signature on a contact-free monitored verification must use
an index already assigned to a different signed hash input. All graph-forgery
alternatives have been eliminated by the actual query-by-query simulation. -/
theorem accepted_fresh_index_reuse (factors : Factors) (base : Hash)
    (history : SecurityForgery.History)
    (honest : ∀ entry ∈ history, entry.2 = evalWithAnswerFn
      (SecurityGraphSigner.answers (privateTable factors)
        (programmed (privateTable factors) (labels factors) base))
      (SecurityIdealSign.signCompact (SecurityGraphExtraction.publicKey factors) entry.1))
    (message : Message) (signature : SignatureEncoding.Compact)
    (fresh : (message, signature) ∉ history)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe factors (SecurityGraphExtraction.Signed factors base history) exposed cache)
    (result : Result Bool)
    (member : some result ∈ support (stopped factors.1 exposed (compile factors.2.2
      (SecurityVerify.verifyCompact (SecurityGraphExtraction.publicKey factors) message signature) exposed cache)))
    (agree : result.2.2.AgreesWithFn base) (accepted : result.1 = true) :
    SecurityGraphExtraction.IndexReuse factors base history message signature := by
  have genuine := completed factors (SecurityGraphExtraction.Signed factors base history) _ _ _ initial
    result member base agree
  rcases SecurityGraphVerifyContact.ideal_forgery_logged factors base history honest message signature
    (genuine.2.1.trans accepted) fresh with reuse | ⟨query, logged, contact⟩
  · exact reuse
  · exact False.elim (genuine.2.2.2 query logged contact)

end SigGolfCandidate.Hypertree.SecurityGraphMonitorVerify
