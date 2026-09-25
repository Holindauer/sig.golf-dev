import SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphCoupling
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphDisclosure SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorNoContact
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical
attribute [local irreducible] recordParsed

/-- The real graph interpreter with the exact common history and atomic budget.
Unlike the passive graph oracle, it always returns the actual graph answer. -/
noncomputable def execute {α : Type} (factors : Factors) (pk : PublicKey) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → ProbComp (Result α)
  | .done value, remaining, exposed, cache, history => pure ⟨some value, remaining, exposed, cache, history⟩
  | .coin n next, remaining, exposed, cache, history => do
      let answer ← $ᵗ Fin (n + 1)
      execute factors pk (next answer) remaining exposed cache history
  | .hash input next, remaining, exposed, cache, history =>
      match remaining with
      | 0 => pure ⟨none, 0, exposed, cache, history⟩
      | remaining + 1 =>
          do
            let result ← (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) input).run cache
            execute factors pk (next result.1) remaining (opened factors exposed input) result.2
              (recordPublic pk history input (cache input).isSome result.1)
  | .sign signPk message next, remaining, exposed, cache, history =>
      if 111596 ≤ remaining then do
        let result ← (randomOracle (spec := HashSpec)
          (SecurityRandomOracle.indexInput signPk message (factors.2.1 message))).run cache
        let index := result.1.extractLsb' 0 160
        let response := SecurityExperiment.serialize
          (SecurityGraphSigner.signature (privateTable factors) (labels factors) (factors.2.1 message) index)
        let opened := revealCache factors.1 (needed factors.2.2 exposed index) exposed
        execute factors pk (next response) (remaining - 111596) opened result.2
          (recordSign history message
            (cache (SecurityRandomOracle.indexInput signPk message (factors.2.1 message))).isSome result.1)
      else pure ⟨none, remaining, exposed, cache, history⟩

/-- Accept the first graph contact as a bad event, retaining the complete ordinary
result on every execution without contact. Budget exhaustion remains a result. -/
def stoppedEvent {α : Type} (event : Result α → Prop) : Option (Result α) → Prop
  | none => True
  | some result => event result

/-- Any event in the actual graph world is included in that event or a contact
in the stopped graph world. This is one union bound in one joint world. -/
theorem execute_le_stopped {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (event : Result α → Prop) :
    Pr[event | execute factors pk view remaining exposed cache history] ≤
      Pr[stoppedEvent event | SecurityMonitorGraphStoppedView.execute factors pk view remaining exposed cache history] := by
  induction view generalizing remaining exposed cache history with
  | done value => simp only [execute, SecurityMonitorGraphStoppedView.execute, probEvent_pure, stoppedEvent, le_refl]
  | coin n next ih =>
    simp only [execute, SecurityMonitorGraphStoppedView.execute, probEvent_bind_eq_tsum]
    apply ENNReal.tsum_le_tsum
    intro answer
    exact mul_le_mul' le_rfl (ih answer remaining exposed cache history ready)
  | hash query next ih =>
    cases remaining with
    | zero => simp only [execute, SecurityMonitorGraphStoppedView.execute, probEvent_pure, stoppedEvent, le_refl]
    | succ remaining =>
      simp only [execute, SecurityMonitorGraphStoppedView.execute]
      by_cases first : inputHit factors exposed query
      · simp only [if_pos first, probEvent_pure, stoppedEvent, if_true]
        exact probEvent_le_one
      · simp only [if_neg first, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases member : result ∈ support ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache)
        · by_cases second : outputHit factors query result.1
          · simp only [if_pos second, probEvent_pure, stoppedEvent, if_true]
            exact mul_le_mul' le_rfl probEvent_le_one
          · simp only [if_neg second]
            have queried := SecurityMonitorGraphStoppedView.read_supported factors history exposed cache ready query result member first second
            exact mul_le_mul' le_rfl (ih result.1 remaining _ result.2 _
              (public_ready factors pk history exposed cache ready query _ queried))
        · have zero := (probOutput_eq_zero_iff _ _).mpr member
          simp only [zero, zero_mul, le_refl]
  | sign signPk message next ih =>
    simp only [execute, SecurityMonitorGraphStoppedView.execute]
    by_cases enough : 111596 ≤ remaining
    · simp only [if_pos enough, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases member : result ∈ support ((randomOracle (spec := HashSpec)
        (SecurityRandomOracle.indexInput signPk message (factors.2.1 message))).run cache)
      · exact mul_le_mul' le_rfl (ih _ (remaining - 111596) _ result.2 _
          (sign_ready factors history exposed cache ready signPk message result.1 result.2 member))
      · have zero := (probOutput_eq_zero_iff _ _).mpr member
        simp only [zero, zero_mul, le_refl]
    · simp only [if_neg enough, probEvent_pure, stoppedEvent, le_refl]

/-- The event and the graph flag share the exact final history. In particular,
`event` can include secret key hits, nonce hits, and index collisions together. -/
theorem execute_le_union {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (event : Result α → Prop) :
    Pr[event | execute factors pk view remaining exposed cache history] ≤
      Pr[fun result => result.bad = true ∨ event result.value |
        run factors.1 exposed (compile factors.2.1 factors.2.2 pk view remaining exposed cache history)] := by
  have bound := execute_le_stopped factors pk view remaining exposed cache history ready event
  have same := SecurityMonitorGraphStoppedView.stopped_compile factors pk view remaining exposed cache history ready
  rw [stopped_eq] at same
  have events := probEvent_congr' (p := stoppedEvent event) (q := stoppedEvent event) (fun _ _ => Iff.rfl) same
  rw [← events, probEvent_map] at bound
  apply bound.trans_eq
  apply probEvent_congr' _ rfl
  intro result _
  cases bad : result.bad <;> simp [keep, bad, stoppedEvent]

/-- The same exact honest-key-generation debit and initial public disclosure as
in the common experiment, interpreted with the true graph oracle. -/
noncomputable def start {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (budget : Nat) : ProbComp (Result α) :=
  if 739 ≤ budget then
    execute factors pk view (budget - 739) (SecurityGraphMonitorSetup.cache factors.1 factors.2.2) ∅ (recordKeygen {})
  else pure ⟨none, budget, ∅, ∅, {}⟩

theorem start_le_union {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (budget : Nat) (event : Result α → Prop) :
    Pr[event | start factors pk view budget] ≤
      Pr[fun result => result.bad = true ∨ event result.value |
        run factors.1 ∅ (SecurityMonitorGraphView.start factors.2.1 factors.2.2 pk view budget)] := by
  unfold start SecurityMonitorGraphView.start
  by_cases enough : 739 ≤ budget
  · simp only [if_pos enough, SecurityGraphMonitorSetup.run_setup]
    exact execute_le_union factors pk view (budget - 739) _ ∅ (recordKeygen {}) (setup_ready factors) event
  · simp only [if_neg enough, run, probEvent_pure, Bool.false_eq_true, false_or, le_refl]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphCoupling.start_le_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms start_le_union

end SigGolfCandidate.Hypertree.SecurityMonitorGraphCoupling
