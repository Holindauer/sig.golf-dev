import SigGolfCandidate.Hypertree.SecurityMonitorView
import SigGolfCandidate.Hypertree.SecurityMonitorIndexState
import SigGolfCandidate.Hypertree.SecurityGraphMonitorSetup

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphView
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraphFactor
  SecurityGraphPassive SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityMonitorView SecurityMonitorIndexState SecurityGraphPublicMonitor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- All public bookkeeping and the exact remaining shared budget travel with the
observable result. The monitor flag and test counter stay outside this record. -/
structure Result (α : Type) where
  value : Option α
  remaining : Nat
  exposed : QueryCache PointSpec
  residual : QueryCache HashSpec
  history : History

/-- Interpret the shared actual-adversary view in the passive graph world.
Only authorized signing disclosures can read point-table coordinates. -/
noncomputable def compile {α : Type} (nonces : NonceTable) (metadata : MetadataTable) (pk : PublicKey) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → Program (Result α)
  | .done value, remaining, exposed, residual, history => .done ⟨some value, remaining, exposed, residual, history⟩
  | .coin n next, remaining, exposed, residual, history =>
      .coin n (fun answer => compile nonces metadata pk (next answer) remaining exposed residual history)
  | .hash input next, remaining, exposed, residual, history =>
      match remaining with
      | 0 => .done ⟨none, 0, exposed, residual, history⟩
      | remaining + 1 => SecurityGraphMonitorOracle.publicStep metadata exposed residual input
          (fun answer opened cache => compile nonces metadata pk (next answer) remaining opened cache
            (recordPublic pk history input (residual input).isSome answer))
  | .sign signPk message next, remaining, exposed, residual, history =>
      if 111596 ≤ remaining then
        let nonce := nonces message
        let input := SecurityRandomOracle.indexInput signPk message nonce
        indexStep residual input (fun answer cache =>
          let index := answer.extractLsb' 0 152
          SecurityGraphMonitorOracle.disclose (needed metadata exposed index) exposed (fun opened =>
            let factors := viewFactors opened metadata
            let signature := SecurityGraphSigner.signature (privateTable factors) (labels factors) nonce index
            compile nonces metadata pk (next (SecurityExperiment.serialize signature)) (remaining - 111596)
              opened cache (recordSign history message (residual input).isSome answer)))
      else .done ⟨none, remaining, exposed, residual, history⟩

/-- Setup is an actual free reveal prefix; key generation still debits all 739
original oracle calls before the first adversary-visible action. -/
noncomputable def start {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (pk : PublicKey) (view : View α) (budget : Nat) : Program (Result α) :=
  if 739 ≤ budget then
    SecurityGraphMonitorSetup.setup metadata (fun exposed =>
      compile nonces metadata pk view (budget - 739) exposed ∅ (recordKeygen {}))
  else .done ⟨none, budget, ∅, ∅, {}⟩

/-- Concrete candidate experiment in the common passive world. This definition
uses the actual adversary, including its private samples and final verifier. -/
noncomputable def experiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) : ProbComp (Outcome (Result SecurityExperiment.Result)) := do
  let nonces ← $ᵗ NonceTable
  let metadata ← $ᵗ MetadataTable
  let pk := truncate (metadata (.node 151 0))
  SecurityGraphMonitorProgram.experiment
    (start nonces metadata pk (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}) budget) ∅

end SigGolfCandidate.Hypertree.SecurityMonitorGraphView
