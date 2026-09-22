import SigGolf.Security

namespace SigGolf
open OracleComp

/-- Static admission: fixed object sizes, strict image-size limits, and nonoverlapping buffers below embedded data. -/
def Submission.Admissible (submission : Submission) : Prop :=
  submission.sizes.Valid ∧ ∀ phase, (submission.image phase).Valid submission.sizes

/-- An unfinished observation cannot satisfy this statement. The strict bound covers every typed input and every fixed oracle, including arbitrary caches, signatures, and witnesses. -/
def Submission.Terminates (submission : Submission) : Prop :=
  ∀ (hash : Hash) (phase : Phase) (input : Input submission.sizes phase),
    let result := submission.runWith hash phase input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT

/-- The same oracle must make the pipeline succeed for all messages. The secret seed is universally quantified, not averaged. -/
def Submission.Complete (submission : Submission) : Prop :=
  ∀ seed, 1 - FAILURE ≤ Pr[fun summary => summary.allSucceed = true |
    withRandomOracle (submission.allMessages seed)]

/-- Maximize over messages before taking expectation over the shared random oracle. Failed phases are charged; unreached phases cost zero. -/
def Submission.CompressionBounds (submission : Submission) : Prop :=
  ∀ seed phase, phase ∈ Phase.budgeted →
    OracleComp.EvalDist.expectedValue (withRandomOracle (submission.allMessages seed))
      (fun summary => ENNReal.ofReal (Real.rpow 2
        ((summary.maxCosts phase : ℝ) / (phase.budget : ℝ)))) ≤ 2

/-- No change of oracle, public key, or message between signing, expansion, and verification. This also covers successful signing with any supplied cache. -/
def Submission.Correct (submission : Submission) : Prop :=
  ∀ (hash : Hash) seed pk cache message signature witness,
    (submission.runWith hash .sign (seed, pk, cache, message)).value = some signature →
    (submission.runWith hash .expand (message, pk, signature)).value = some witness →
    (submission.runWith hash .verify (message, pk, witness)).value = some ()

/-- Scored cycles cover successful honest pipelines. Arbitrary inputs remain subject to the universal termination bound. -/
def Submission.VerificationBound (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) seed message,
    let result := evalWithAnswerFn hash (submission.honest seed message)
    result.success = true → result.verificationCycles ≤ C

/-- The organizer-owned competition claim, parameterized by the exact four images, fixed sizes, and claimed verification bound. The loader and interpreter enforce fixed-size outputs, memory limits, and fresh stateless executions. -/
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admissible : submission.Admissible
  termination : submission.Terminates
  completeness : submission.Complete
  compressionBounds : submission.CompressionBounds
  correctness : submission.Correct
  security : submission.Secure
  verificationBound : submission.VerificationBound C

end SigGolf
