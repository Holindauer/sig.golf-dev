import SigGolfCandidate.Hypertree.SecurityMonitorIndexView

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexTrace
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorSign SecurityMonitorView SecurityMonitorIndexState SecurityIndexTrace
  SecurityMonitorGraphView SecurityMonitorIndexLift SecurityGraphPublicMonitor SecurityMonitorIndexView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The syntax monitor records exactly the fresh H5 suffix of the public history. -/
def Aligned {α : Type} (program : SecurityIndexProgram.Program α) (traceOf : α → List Entry) (before : List Entry) : Prop :=
  ∀ result ∈ support (SecurityIndexProgram.execute program), traceOf result.1 = before ++ result.2

theorem aligned_pure {α : Type} (value : α) (traceOf : α → List Entry) :
    Aligned (.pure value) traceOf (traceOf value) := by
  intro result member
  simp only [SecurityIndexProgram.execute, support_pure, Set.mem_singleton_iff] at member
  subst result
  simp only [List.append_nil]

theorem aligned_coin {α : Type} (n : Nat) (next : Fin (n+1) → SecurityIndexProgram.Program α)
    (traceOf : α → List Entry) (before : List Entry)
    (aligned : ∀ answer, Aligned (next answer) traceOf before) : Aligned (.coin n next) traceOf before := by
  intro result member
  simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
  obtain ⟨answer, _, member⟩ := member
  exact aligned answer result member

theorem aligned_draw {α : Type} (mark : Bool) (next : BitVec 256 → SecurityIndexProgram.Program α)
    (traceOf : α → List Entry) (before : List Entry)
    (aligned : ∀ answer, Aligned (next answer) traceOf (before ++ [(mark,answer.extractLsb' 0 160)])) :
    Aligned (.draw mark next) traceOf before := by
  intro result member
  simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
  obtain ⟨answer, _, member⟩ := member
  simp only [support_map, Set.mem_image] at member
  obtain ⟨tail, member, same⟩ := member
  cases same
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using aligned answer tail member

theorem aligned_ofGraph {α β : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (program : SecurityGraphMonitorProgram.Program α) (next : α → SecurityIndexProgram.Program β)
    (traceOf : β → List Entry) (before : List Entry)
    (aligned : ∀ value, Aligned (next value) traceOf before) :
    Aligned (ofGraph table cache program next) traceOf before := by
  intro result member
  rw [execute_ofGraph] at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨value, _, member⟩ := member
  exact aligned value.value result member

theorem public_trace_none (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256)
    (absent : (SecurityIndexQuery.parse pk query).isSome = false) :
    (recordPublic pk history query cached answer).indexTrace = history.indexTrace := by
  have empty : SecurityIndexQuery.parse pk query = none := by
    cases found : SecurityIndexQuery.parse pk query with
    | none => rfl
    | some pair => simp only [found, Option.isSome_some, Bool.true_eq_false] at absent
  change (recordParsed history query _ _ cached answer).indexTrace = _
  rw [empty]
  cases decide (SecuritySeparation.SeedEligible query) <;> rfl

theorem public_trace_some (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256)
    (present : (SecurityIndexQuery.parse pk query).isSome = true) :
    (recordPublic pk history query cached answer).indexTrace =
      if cached then history.indexTrace else history.indexTrace ++ [(false,answer.extractLsb' 0 160)] := by
  change (recordParsed history query _ _ cached answer).indexTrace = _
  cases parsed : SecurityIndexQuery.parse pk query with
  | none => simp only [parsed, Option.isSome_none, Bool.false_eq_true] at present
  | some pair => cases pair; rfl

/-- Every concrete compiler path records precisely the trace monitored by the
index probability theorem, including cached probes and repeated signing. -/
theorem compile_aligned {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec) (history : History) :
    Aligned (SecurityMonitorIndexView.compile table nonces metadata pk view remaining exposed residual history)
      (fun result => result.history.indexTrace) history.indexTrace := by
  induction view generalizing remaining exposed residual history with
  | done value => exact aligned_pure _ _
  | coin n next ih => exact aligned_coin n _ _ _ (fun answer => ih answer _ _ _ _)
  | hash input next ih =>
    cases remaining with
    | zero => exact aligned_pure _ _
    | succ remaining =>
      rw [SecurityMonitorIndexView.compile]
      split
      next parsed =>
        cases found : residual input with
        | some answer =>
          rw [drawCached, found]
          have trace := public_trace_some pk history input (residual input).isSome answer parsed
          simp only [found, Option.isSome_some, if_true] at trace
          rw [← trace]
          exact ih answer _ _ _ _
        | none =>
          rw [drawCached, found]
          apply aligned_draw
          intro answer
          have trace := public_trace_some pk history input (residual input).isSome answer parsed
          simp only [found, Option.isSome_none, Bool.false_eq_true, if_false] at trace
          rw [← trace]
          exact ih answer _ _ _ _
      next absent =>
        apply aligned_ofGraph
        intro result
        have missing : (SecurityIndexQuery.parse pk input).isSome = false := Bool.eq_false_iff.mpr absent
        rw [← public_trace_none pk history input (residual input).isSome result.1 missing]
        exact ih result.1 _ _ _ _
  | sign signPk message next ih =>
    rw [SecurityMonitorIndexView.compile]
    split
    next enough =>
      dsimp only
      cases found : residual (SecurityRandomOracle.indexInput signPk message (nonces message)) with
      | some answer =>
        rw [drawCached, found]
        have trace : (recordSign history message true answer).indexTrace = history.indexTrace := rfl
        simp only [found, Option.isSome_some]
        rw [← trace]
        exact ih _ _ _ _ _
      | none =>
        rw [drawCached, found]
        apply aligned_draw
        intro answer
        simp only [found, Option.isSome_none]
        exact ih _ _ _ _ _
    next insufficient => exact aligned_pure _ _

theorem start_aligned {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) :
    Aligned (SecurityMonitorIndexView.start table nonces metadata pk view budget)
      (fun result => result.history.indexTrace) [] := by
  rw [SecurityMonitorIndexView.start]
  split
  · exact compile_aligned _ _ _ _ _ _ _ _ _
  · exact aligned_pure _ _

#print axioms start_aligned
end SigGolfCandidate.Hypertree.SecurityMonitorIndexTrace
