import SigGolfCandidate.Hypertree.SecurityMonitorNonceHistory

namespace SigGolfCandidate.Hypertree.SecurityMonitorNonceView
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev JointResult := NonceTable × SecurityGraphMonitorProgram.Outcome (Result SecurityExperiment.Result)

/-- One common simulation with its hidden nonce table retained for passive event
classification. Dropping that table gives exactly the original graph experiment. -/
noncomputable def joint (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp JointResult := do
  let nonces ← $ᵗ NonceTable
  let metadata ← $ᵗ MetadataTable
  let points ← $ᵗ PointTable
  let pk := truncate (metadata (.node 159 0))
  let outcome ← SecurityGraphMonitorProgram.run points ∅
    (SecurityMonitorGraphView.start nonces metadata pk
      (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}) budget)
  pure (nonces, outcome)

/-- Exact marginal: the same final attacker output, histories, graph hit flag,
and graph test count are preserved jointly. -/
theorem joint_marginal (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Prod.snd <$> joint publicCache adversary rounds budget =
      SecurityMonitorGraphView.experiment publicCache adversary rounds budget := by
  simp only [joint, SecurityMonitorGraphView.experiment, SecurityGraphMonitorProgram.experiment,
    map_bind, map_pure, bind_pure]
  rfl

noncomputable def jointAnnotation (result : JointResult) : NO (Result SecurityExperiment.Result) :=
  annotate result.1 result.2.value

/-- The same simulation ordered so the nonce monitor sees arbitrary independent
initial point and metadata tables, followed by a fresh uniform nonce table. -/
noncomputable def nonceExperiment (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp (NO (Result SecurityExperiment.Result)) := do
  let metadata ← $ᵗ MetadataTable
  let points ← $ᵗ PointTable
  let pk := truncate (metadata (.node 159 0))
  SecurityNonceProgram.execute
    (start points metadata pk (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}) budget) ∅

private theorem nonce_swap {α : Type} (next : NonceTable → MetadataTable → PointTable → ProbComp α) :
    𝒮[(do let nonces ← $ᵗ NonceTable; let metadata ← $ᵗ MetadataTable; let points ← $ᵗ PointTable
           next nonces metadata points)] =
      𝒮[(do let metadata ← $ᵗ MetadataTable; let points ← $ᵗ PointTable; let nonces ← $ᵗ NonceTable
             next nonces metadata points)] := by
  calc
    _ = 𝒮[(do let metadata ← $ᵗ MetadataTable; let nonces ← $ᵗ NonceTable; let points ← $ᵗ PointTable
               next nonces metadata points)] := evalSPMF_bind_bind_swap _ _ _
    _ = _ := by
      apply evalSPMF_bind_congr
      intro metadata _
      exact evalSPMF_bind_bind_swap _ _ _

/-- Full joint identification of nonce hits/costs with the actual common
simulation's final history, rather than a cost from a different game hop. -/
theorem joint_annotation (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    𝒮[jointAnnotation <$> joint publicCache adversary rounds budget] =
      𝒮[nonceExperiment publicCache adversary rounds budget] := by
  simp only [joint, nonceExperiment, execute_start, map_bind, bind_pure_comp,
    SecurityGraphMonitorObserve.observe, Functor.map_map]
  exact nonce_swap (fun nonces metadata points =>
    (jointAnnotation ∘ (fun outcome => (nonces, outcome))) <$>
      SecurityGraphMonitorProgram.run points ∅ (SecurityMonitorGraphView.start nonces metadata
        (truncate (metadata (.node 159 0)))
        (ofInteract adversary (truncate (metadata (.node 159 0))) rounds
          (adversary.initial (truncate (metadata (.node 159 0))) publicCache) {}) budget))

theorem nonceExperiment_bound (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result => result.bad = true | nonceExperiment publicCache adversary rounds budget] ≤
      expectedValue (nonceExperiment publicCache adversary rounds budget)
        (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256 := by
  have bound := SecurityNonceProgram.mixed_prob_bad_le_expected
    (do let metadata ← $ᵗ MetadataTable; let points ← $ᵗ PointTable; pure (metadata, points))
    (fun pair => let pk := truncate (pair.1 (.node 159 0))
      start pair.2 pair.1 pk (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}) budget)
    (fun _ => ∅)
  simpa only [nonceExperiment, bind_assoc, pure_bind] using bound

/-- Private nonce prediction is bounded by the expected number of the common
history's prereveal guesses, preserving the shared output distribution. -/
theorem joint_nonce_bound (publicCache : SigGolf.Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result => hits result.1 result.2.value.history = true | joint publicCache adversary rounds budget] ≤
      expectedValue (joint publicCache adversary rounds budget)
        (fun result => (result.2.value.history.nonceGuesses.length : ENNReal)) / (2 : ENNReal)^256 := by
  have same := joint_annotation publicCache adversary rounds budget
  have event := probEvent_congr' (p := fun result => result.bad = true) (q := fun result => result.bad = true)
    (fun _ _ => Iff.rfl) same
  have cost : expectedValue (jointAnnotation <$> joint publicCache adversary rounds budget)
      (fun result => (result.guesses : ENNReal)) =
      expectedValue (nonceExperiment publicCache adversary rounds budget) (fun result => (result.guesses : ENNReal)) := by
    apply expectedValue_congr _ _
    intro result
    exact probOutput_congr rfl same
  rw [probEvent_map] at event
  rw [expectedValue_map] at cost
  have bound := nonceExperiment_bound publicCache adversary rounds budget
  rw [← event, ← cost] at bound
  exact bound

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorNonceView.joint_nonce_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms joint_nonce_bound

end SigGolfCandidate.Hypertree.SecurityMonitorNonceView
