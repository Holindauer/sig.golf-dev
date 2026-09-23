import SigGolfCandidate.Hypertree.SecuritySeedTraceHistory
import SigGolfCandidate.Hypertree.SecuritySeedMonitor

namespace SigGolfCandidate.Hypertree.SecurityMonitorSeedInputs
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphCoupling
  SecuritySeparation SecuritySeed
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false
attribute [local irreducible] recordParsed

/-- Every recorded seed probe lies in a real seed-derivation domain. -/
def Eligible (history : History) : Prop := ∀ query ∈ history.seedInputs, SeedEligible query

@[simp] theorem eligible_empty : Eligible {} := by intro query member; cases member

theorem Eligible.recordPublic {history : History} (eligible : Eligible history) (pk : PublicKey)
    (query : Query) (cached : Bool) (answer : BitVec 256) : Eligible (SecurityMonitorIndexState.recordPublic pk history query cached answer) := by
  intro other member
  rw [SecuritySeedTraceView.public_seedInputs] at member
  split at member
  next domain =>
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ domain
    · exact eligible other later
  next outside => exact eligible other member

theorem Eligible.recordSign {history : History} (eligible : Eligible history) (message : Message)
    (cached : Bool) (answer : BitVec 256) : Eligible (SecurityMonitorIndexState.recordSign history message cached answer) := eligible

theorem execute_eligible {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (eligible : Eligible history) (result : Result α)
    (member : result ∈ support (execute factors pk view remaining exposed cache history)) : Eligible result.history := by
  induction view generalizing remaining exposed cache history with
  | done value =>
    simp only [execute, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact eligible
  | coin n next ih =>
    rw [execute, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    exact ih answer remaining exposed cache history eligible member
  | hash query next ih =>
    cases remaining with
    | zero =>
      simp only [execute, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact eligible
    | succ remaining =>
      rw [execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer.1 remaining _ answer.2 _ (eligible.recordPublic pk query _ answer.1) member
  | sign signPk message next ih =>
    rw [execute] at member
    split at member
    next enough =>
      rw [mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih _ (remaining-117508) _ answer.2 _ (eligible.recordSign message _ answer.1) member
    next short =>
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst result
      exact eligible

theorem start_eligible {α : Type} (factors : Factors) (pk : PublicKey) (view : View α)
    (budget : Nat) (result : Result α) (member : result ∈ support (SecurityMonitorGraphCoupling.start factors pk view budget)) :
    Eligible result.history := by
  rw [SecurityMonitorGraphCoupling.start] at member
  split at member
  · exact execute_eligible factors pk view _ _ _ (recordKeygen {})
      (show Eligible (recordKeygen {}) from eligible_empty) result member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst result
    exact eligible_empty

/-- Chronological trace order and the passive history's reverse order describe
exactly the same seed-contact event. -/
theorem hit_reverse_iff (history : History) (eligible : Eligible history) (seed : Seed) :
    SeedHitTrace history.seedInputs.reverse seed ↔ SecuritySeedMonitor.Hit history.seedInputs seed := by
  simp only [SeedHitTrace, SecuritySeedMonitor.Hit, List.mem_reverse, SecuritySeedMonitor.mem_eligible]
  constructor
  · rintro ⟨query, member, hit⟩
    exact ⟨query, ⟨member,eligible query member⟩,hit⟩
  · rintro ⟨query, ⟨member,_⟩, hit⟩
    exact ⟨query,member,hit⟩

#print axioms start_eligible
end SigGolfCandidate.Hypertree.SecurityMonitorSeedInputs
