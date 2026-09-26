import SigGolfCandidate.Hypertree.SecuritySecretKeyTraceHistory

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphFactor SecurityGraphPassive
  SecurityBudget SecuritySecretKeyTraceBlocks SecurityMonitorViewAtomic SecurityGraphState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def handler (factors : Factors) :=
  gameImplementation (privateTable factors) (labels factors)

noncomputable def traced {α : Type} (factors : Factors) (program : OracleComp GameWorld α)
    (budget : Nat) (cache : QueryCache HashSpec) : ProbComp (Option α × List Query) :=
  (simulateQ (handler factors) (tracePublic (cutoff program budget))).run' cache

private theorem public_run (factors : Factors) (input : Query) (cache : QueryCache HashSpec) :
    (simulateQ (handler factors) (liftM (GameWorld.query (.inr (.inr input))))).run cache =
      (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) input).run cache := by
  rw [handler, routing]
  simp only [SecurityGraphIdeal.fixPrivate, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, SecurityGraphIdeal.privateImplementation,
    SecurityGraphOracle.implementation, QueryImpl.add_apply_inr]

private theorem coin_run (factors : Factors) (n : Nat) (cache : QueryCache HashSpec) :
    (simulateQ (handler factors) (liftM (GameWorld.query (.inl n)))).run cache =
      (fun answer => (answer, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  rw [handler, routing]
  rfl

private theorem sign_run (factors : Factors) (pk : PublicKey) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ (handler factors) ((SecurityExperiment.signWire pk message).liftComp GameWorld)).run cache =
      (fun result => (SecurityExperiment.serialize (SecurityGraphSigner.signature (privateTable factors)
        (labels factors) (factors.2.1 message) (result.1.extractLsb' 0 160)), result.2)) <$>
        (randomOracle (spec := HashSpec) (SecurityRandomOracle.indexInput pk message (factors.2.1 message))).run cache := by
  rw [handler, routing, routed_signWire_run]
  rfl

/-- Exact traced cutoff semantics in the true graph world, preserving ordinary
budget failures and the complete secret key log. The log is chronological; the public
history records those same entries in reverse order. -/
theorem traced_view {α : Type} (factors : Factors) (pk : PublicKey) (view : View α) (budget : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History) :
    𝒮[extend history <$> traced factors (realize view) budget cache] =
      𝒮[project <$> SecurityMonitorGraphCoupling.execute factors pk view budget exposed cache history] := by
  induction view generalizing budget exposed cache history with
  | done value =>
    simp [traced, realize, tracePublic_pure, SecurityMonitorGraphCoupling.execute, project, extend]
  | hash input next ih =>
    cases budget with
    | zero =>
      rw [traced, realize, cutoff_query_bind]
      simp [charge, tracePublic_pure, SecurityMonitorGraphCoupling.execute, project, extend]
    | succ budget =>
      rw [SecurityMonitorGraphCoupling.execute]
      simp only [traced, realize, cutoff_query_bind, charge, Nat.succ_le_succ_iff,
        Nat.zero_le, if_true, Nat.add_sub_cancel, tracePublic_query_bind, run_bind,
        public_run, bind_pure_comp, run_map, map_bind, Functor.map_map]
      apply evalSPMF_bind_congr
      intro result _
      simp only [extend_public pk history input (cache input).isSome result.1]
      exact ih result.1 budget _ result.2 _
  | coin n next ih =>
    rw [traced, realize, cutoff_query_bind]
    simp only [charge, Nat.zero_le, if_true, Nat.sub_zero]
    rw [tracePublic_query_bind]
    simp only [prependPublic, Prod.mk.eta, bind_pure]
    rw [run_bind, coin_run, SecurityMonitorGraphCoupling.execute]
    simp only [bind_map_left, map_bind]
    apply evalSPMF_bind_congr
    intro answer _
    exact ih answer budget exposed cache history
  | sign signPk message next ih =>
    have safe := lift_clean (SecuritySecretKeyHonest.signWire signPk message)
    have fixed := SecurityAtomicCounts.signWire signPk message
    rw [SecurityMonitorGraphCoupling.execute]
    by_cases enough : 117508 ≤ budget
    · rw [if_pos enough]
      simp only [traced, realize]
      rw [trace_enough safe fixed _ budget enough, run_bind]
      rw [sign_run]
      simp only [bind_map_left, map_bind]
      apply evalSPMF_bind_congr
      intro result _
      simpa only [extend_sign, traced] using ih
        (SecurityExperiment.serialize (SecurityGraphSigner.signature (privateTable factors) (labels factors)
          (factors.2.1 message) (result.1.extractLsb' 0 160))) (budget - 117508)
        (SecurityGraphDisclosure.revealCache factors.1
          (SecurityGraphMonitorSign.needed factors.2.2 exposed (result.1.extractLsb' 0 160)) exposed)
        result.2 (recordSign history message
          (cache (SecurityRandomOracle.indexInput signPk message (factors.2.1 message))).isSome result.1)
    · rw [if_neg enough]
      simp only [traced, realize, evalSPMF_map]
      rw [trace_insufficient safe fixed (handler factors) _ budget cache (by omega)]
      simp [project, extend]

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView.traced_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms traced_view
end SigGolfCandidate.Hypertree.SecuritySecretKeyTraceView
