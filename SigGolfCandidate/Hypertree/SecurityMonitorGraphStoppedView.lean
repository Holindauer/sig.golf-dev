import SigGolfCandidate.Hypertree.SecurityMonitorGraphState
import SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphDisclosure SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorMetadata
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorNoContact SecurityGraphMonitorChainState
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical
attribute [local irreducible] recordParsed

/-- Mathematical stopped execution through the actual graph oracle. Secret
coordinates are inspected only to define the stopping events, never to supply
extra information to the passive simulator's continuation. -/
noncomputable def execute {α : Type} (factors : Factors) (pk : PublicKey) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → ProbComp (Option (Result α))
  | .done value, remaining, exposed, cache, history => pure (some ⟨some value, remaining, exposed, cache, history⟩)
  | .coin n next, remaining, exposed, cache, history => do
      let answer ← $ᵗ Fin (n + 1)
      execute factors pk (next answer) remaining exposed cache history
  | .hash input next, remaining, exposed, cache, history =>
      match remaining with
      | 0 => pure (some ⟨none, 0, exposed, cache, history⟩)
      | remaining + 1 =>
          if inputHit factors exposed input then pure none else do
            let result ← (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) input).run cache
            if outputHit factors input result.1 then pure none else
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
      else pure (some ⟨none, remaining, exposed, cache, history⟩)

theorem stopped_indexStep {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α) :
    stopped table exposed (indexStep cache query next) =
      ((randomOracle (spec := HashSpec) query).run cache >>= fun result => stopped table exposed (next result.1 result.2)) := by
  cases present : cache query <;> simp only [indexStep, present, stopped, randomOracle.run_eq, pure_bind, bind_assoc]

/-- A supported real graph query that misses both contacts appears as a normal
read in the operational monitor; its exact state can feed the next induction step. -/
theorem read_supported (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (ready : Ready factors history exposed cache) (query : Query)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache))
    (first : ¬inputHit factors exposed query) (second : ¬outputHit factors query result.1) :
    some (result.1, opened factors exposed query, result.2) ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => Program.done (answer, opened, residual)))) := by
  rw [stopped_public_oracle _ _ _ _ _ ready.1.1 ready.1.2.2, if_neg first, mem_support_bind_iff]
  refine ⟨result, member, ?_⟩
  simp only [if_neg second, stopped, support_pure, Set.mem_singleton_iff]

/-- Exact full adaptive-view coupling. This is the actual shared compiler, with
signing responses, both caches, history, remaining budget, and every private coin
preserved up to the first graph contact. -/
theorem stopped_compile {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) :
    𝒮[stopped factors.1 exposed
      (compile factors.2.1 factors.2.2 pk view remaining exposed cache history)] =
      𝒮[execute factors pk view remaining exposed cache history] := by
  induction view generalizing remaining exposed cache history with
  | done value => rfl
  | coin n next ih =>
    simp only [compile, execute, stopped]
    apply evalSPMF_bind_congr
    intro answer _
    exact ih answer remaining exposed cache history ready
  | hash query next ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      simp only [compile, execute]
      rw [stopped_public_oracle _ _ _ _ _ ready.1.1 ready.1.2.2]
      by_cases first : inputHit factors exposed query
      · simp only [if_pos first]
      · simp only [if_neg first]
        apply evalSPMF_bind_congr
        intro result member
        by_cases second : outputHit factors query result.1
        · simp only [if_pos second]
        · simp only [if_neg second]
          have queried := read_supported factors history exposed cache ready query result member first second
          exact ih result.1 remaining _ result.2 _
            (public_ready factors pk history exposed cache ready query _ queried)
  | sign signPk message next ih =>
    simp only [compile, execute]
    by_cases enough : 111596 ≤ remaining
    · simp only [if_pos enough]
      rw [stopped_indexStep]
      apply evalSPMF_bind_congr
      intro result member
      rw [stopped_disclose]
      rw [opened_signature factors.1 factors.2.1 factors.2.2 exposed ready.2]
      exact ih _ (remaining - 111596) _ result.2 _
        (sign_ready factors history exposed cache ready signPk message result.1 result.2 member)
    · simp only [if_neg enough, stopped]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView.stopped_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stopped_compile
end SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
