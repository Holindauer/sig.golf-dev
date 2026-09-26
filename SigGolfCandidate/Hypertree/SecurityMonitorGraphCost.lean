import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorCredit

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphCost
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFactor SecurityGraphPassive SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityIndexQuery
  SecuritySeparation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

theorem located_not_secretKey (query : Query) (position : Position) (located : locate query = some position) :
    ¬SecretKeyEligible query := by
  unfold locate at located
  split at located
  next found =>
    obtain ⟨payload, equal⟩ := found.choose_spec
    rw [← equal]
    cases found.choose with
    | chain address step => exact SecurityDomains.not_secretKeyEligible_addressedInput 2 _ _ _ _ _ _ (by decide) (by decide)
    | leaf level tree side => exact SecurityDomains.not_secretKeyEligible_addressedInput 3 _ _ _ _ _ _ (by decide) (by decide)
    | node level tree => exact SecurityDomains.not_secretKeyEligible_addressedInput 4 _ _ _ _ _ _ (by decide) (by decide)
  next absent => cases located

theorem parsed_graph_mono (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible cached : Bool) (answer : BitVec 256) :
    history.counts.graph ≤ (recordParsed history query parsed secretKeyEligible cached answer).counts.graph := by
  cases parsed with
  | some pair => exact Nat.le_refl _
  | none =>
    cases secretKeyEligible <;> simp only [recordParsed, Bool.false_eq_true, if_false, if_true] <;> omega

attribute [local irreducible] recordParsed

theorem public_graph_mono (pk : PublicKey) (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    history.counts.graph ≤ (recordPublic pk history query cached answer).counts.graph :=
  parsed_graph_mono history query (parse pk query) (decide (SecretKeyEligible query)) cached answer

theorem public_graph_located (pk : PublicKey) (history : History) (query : Query) (cached : Bool)
    (answer : BitVec 256) (position : Position) (located : locate query = some position) :
    (recordPublic pk history query cached answer).counts.graph = history.counts.graph + 1 := by
  have unparsed : parse pk query = none := by
    cases parsed : parse pk query with
    | none => rfl
    | some pair =>
      have serialized := (parse_some_iff pk query pair).mp parsed
      have outside := locate_index pk pair.1 pair.2
      rw [serialized, located] at outside
      cases outside
  change (recordParsed history query (parse pk query) (decide (SecretKeyEligible query)) cached answer).counts.graph = _
  rw [unparsed]
  simp only [decide_eq_false (located_not_secretKey query position located), recordParsed, Bool.false_eq_true, if_false]

/-- The shared query classifier spends graph credits only on its own class.
Secret key and parsed-index queries pass through with zero graph-contact tests. -/
theorem public_record_credit {α : Type} (allowance : α → Nat) (pk : PublicKey) (history : History)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance
      (2 * (recordPublic pk history query (cache query).isSome answer).counts.graph) (next answer opened residual)) :
    Credit allowance (2 * history.counts.graph)
      (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  cases located : locate query with
  | none =>
    apply publicStep_outside_credit _ _ _ _ _ _ _ located
    intro answer opened residual
    exact Credit.weaken allowance _ (Nat.mul_le_mul_left 2 (public_graph_mono pk history query _ answer))
      (credit answer opened residual)
  | some position =>
    apply publicStep_credit
    intro answer opened residual
    have nextCredit := credit answer opened residual
    rw [public_graph_located pk history query _ answer position located] at nextCredit
    convert nextCredit using 1 <;> omega

theorem indexStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (cache : QueryCache HashSpec) (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α)
    (credit : ∀ answer residual, Credit allowance spent (next answer residual)) :
    Credit allowance spent (indexStep cache query next) := by
  unfold indexStep
  cases cache query with
  | some answer => exact credit answer cache
  | none => exact fun answer => credit answer _

/-- Actual graph tests are charged to graph-class calls in the same adaptive
execution, preserving the secret key and index portions of the shared budget. -/
theorem compile_credit {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) :
    Credit (fun result : Result α => 2 * result.history.counts.graph) (2 * history.counts.graph)
      (compile nonces metadata pk view remaining exposed cache history) := by
  induction view generalizing remaining exposed cache history with
  | done value => exact Nat.le_refl _
  | coin n next ih => exact fun answer => ih answer remaining exposed cache history
  | hash query next ih =>
    cases remaining with
    | zero => exact Nat.le_refl _
    | succ remaining =>
      apply public_record_credit
      intro answer opened residual
      exact ih answer remaining opened residual _
  | sign signPk message next ih =>
    unfold compile
    split
    next enough =>
      apply indexStep_credit
      intro answer residual
      apply disclose_credit
      intro opened
      apply Credit.weaken _ _ _ (ih _ (remaining - 117508) opened residual
        (recordSign history message (cache (SecurityRandomOracle.indexInput signPk message (nonces message))).isSome answer))
      change 2 * history.counts.graph ≤ 2 * (history.counts.graph + 117507)
      omega
    next short => exact Nat.le_refl _

theorem start_credit {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (budget : Nat) :
    Credit (fun result : Result α => 2 * result.history.counts.graph) 0
      (start nonces metadata pk view budget) := by
  unfold start
  split
  next enough =>
    apply disclose_credit
    intro exposed
    exact Credit.weaken _ _ (Nat.zero_le _)
      (compile_credit nonces metadata pk view (budget - 739) exposed ∅ (recordKeygen {}))
  next short => exact Nat.zero_le _

/-- Pathwise graph-counter domination in the actual common passive execution. -/
theorem start_tests_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (budget : Nat) (result : Outcome (Result α))
    (member : result ∈ support (SecurityGraphMonitorProgram.experiment (start nonces metadata pk view budget) ∅)) :
    result.tests ≤ 2 * result.value.history.counts.graph := by
  rw [SecurityGraphMonitorProgram.experiment, mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  simpa only [Nat.zero_add] using run_credit _ _ 0 (start_credit nonces metadata pk view budget) _ _ result member

/-- Graph-contact probability uses only graph-class charged calls in this same
simulation. The nonce/index and secret key classes retain their own budget shares. -/
theorem start_bad_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey)
    (view : View α) (budget : Nat) :
    Pr[fun result => result.bad = true |
      SecurityGraphMonitorProgram.experiment (start nonces metadata pk view budget) ∅] ≤
      2 * expectedValue (SecurityGraphMonitorProgram.experiment (start nonces metadata pk view budget) ∅)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128 := by
  apply (prob_bad_le_expected (start nonces metadata pk view budget) ∅).trans
  apply ENNReal.div_le_div _ le_rfl
  calc
    _ ≤ expectedValue (SecurityGraphMonitorProgram.experiment (start nonces metadata pk view budget) ∅)
        (fun result => 2 * (result.value.history.counts.graph : ENNReal)) := by
      apply expectedValue_mono_of_support
      intro result member
      exact_mod_cast start_tests_le nonces metadata pk view budget result member
    _ = _ := by simp only [mul_comm (2 : ENNReal), expectedValue_mul_const]

/-- The fully concrete adversary experiment inherits the graph bound with its
own expected graph-class count; there is no cost transfer across a bad event. -/
theorem experiment_bad_le (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result => result.bad = true | SecurityMonitorGraphView.experiment publicCache adversary rounds budget] ≤
      2 * expectedValue (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128 := by
  unfold SecurityMonitorGraphView.experiment
  simp only [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ NonceTable) (fun nonces => expectedValue ($ᵗ MetadataTable) (fun metadata =>
      2 * expectedValue (SecurityGraphMonitorProgram.experiment
        (start nonces metadata (truncate (metadata (.node 159 0)))
          (ofInteract adversary (truncate (metadata (.node 159 0))) rounds
            (adversary.initial (truncate (metadata (.node 159 0))) publicCache) {}) budget) ∅)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128)) := by
      apply expectedValue_mono
      intro nonces
      apply expectedValue_mono
      intro metadata
      exact start_bad_le nonces metadata _ _ budget
    _ = _ := by
      simp only [div_eq_mul_inv, mul_comm (2 : ENNReal), expectedValue_mul_const]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphCost.experiment_bad_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_bad_le

end SigGolfCandidate.Hypertree.SecurityMonitorGraphCost
