import LeanSphincs.Benchmark.SchemeInterface
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! Scheme-parametric SUF-CMA game, adapted from leanVM-b's xmss-fv
Statement.lean (0e82ea922c570b8c4d706a06bc3dc7caf3b34ff0).
There is no epoch restriction: repeated adaptive requests are permitted. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Benchmark

abbrev SigningSpec := Message →ₒ Option Bytes

structure Forgery where
  message : Message
  signature : Bytes
deriving DecidableEq

structure Adversary where
  main : Bytes → OracleComp (OracleWorld + SigningSpec) Forgery

def IsReplay (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (IsReplay log forgery) :=
  inferInstanceAs (Decidable
    (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

def signingOracle (S : SigScheme) (sk : S.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging (S.sign sk)

def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

def gameCore (S : SigScheme) (A : Adversary) : OracleComp OracleWorld Bool := do
  let (pk, sk) ← S.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle S sk) (A.main pk)).run
  let verified ← liftM (S.verify pk forgery.message forgery.signature)
  return decide (¬ IsReplay log forgery) && verified

noncomputable def sufAdvantage (S : SigScheme) (A : Adversary) : ℝ≥0∞ :=
  Pr[= true | runROM (gameCore S A)]

/-- Raw oracle calls across keygen, the adversary, signing and final verify.
This is the security budget, not the block-weighted verification score. -/
def HasHashQueryBound (S : SigScheme) (A : Adversary) (qH : Nat) : Prop :=
  (gameCore S A).IsQueryBoundP (· matches .inr _) qH

/-- Bound signing requests on every adversarial path for every public key.
Repeated requests and failed responses consume budget just like successful
requests for distinct messages. -/
def HasSigningQueryBound (A : Adversary) (qS : Nat) : Prop :=
  ∀ pk, (A.main pk).IsQueryBoundP (· matches .inr _) qS

#guard IsReplay [⟨0, some [1]⟩] ⟨0, [1]⟩
#guard ¬ IsReplay [⟨0, some [1]⟩] ⟨0, [2]⟩
#guard ¬ IsReplay [⟨0, some [1]⟩] ⟨1, [1]⟩
#guard ¬ IsReplay [⟨0, none⟩] ⟨0, []⟩
#guard ¬ IsReplay [⟨0, none⟩] ⟨0, [1]⟩

end LeanSphincs.Benchmark
