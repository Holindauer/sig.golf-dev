import LeanSphincs.Benchmark.Target
import VCVio.OracleComp.ProbComp

/-! Non-cryptographic fixtures, not an accepted baseline. The counterexample
uses an intentionally enormous unary public key to expose the quantifier error;
it claims only the old availability property, not the wire-size or security gates. -/
open LeanSphincs.Benchmark OracleComp OracleSpec ENNReal ProbComp
namespace LeanSphincsTest.AdaptiveAvailability

def forbidden : SigScheme where
  SecretKey := Fin (2 ^ 256)
  keygen := do
    let k ← liftM (uniformFin (2 ^ 256 - 1))
    return (List.replicate k.val 0, k)
  sign := fun k message => pure (if k = message.toFin then none else some [])
  verify := fun _ _ _ => pure true

def chooseForbidden : SigningParticipant where
  main := fun pk => do
    let _ ← (OracleWorld + SigningSpec).query (.inr (BitVec.ofNat 256 pk.length))
    pure ()

lemma old_experiment (message : Message) :
    runROM (signingFailureExperiment forbidden message) =
      (fun k : Fin (2 ^ 256) => decide (k = message.toFin)) <$> uniformFin (2 ^ 256 - 1) := by
  simp [signingFailureExperiment, forbidden, runROM, romImpl,
    roSim.run_liftM, monad_norm]
  congr 1
  funext k
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

/-- Every fixed message fails with probability exactly 2^-256. -/
theorem old_certificate : HasSigningFailureBound forbidden 256 := by
  intro message
  rw [old_experiment]
  simp [probOutput_map, probEvent_eq_eq_probOutput, probOutput_uniformFin]
  norm_num

lemma interaction : signingInteraction forbidden chooseForbidden =
    (fun k : Fin (2 ^ 256) => [⟨BitVec.ofNat 256 k.val, none⟩]) <$>
      (liftM (uniformFin (2 ^ 256 - 1)) : OracleComp OracleWorld _) := by
  simp [signingInteraction, forbidden, chooseForbidden, signingOracle,
    QueryImpl.withLogging, QueryImpl.withTraceAppend, monad_norm, BitVec.toFin_ofNat,
    Fin.ofNat_eq_cast, List.length_replicate]
  congr 1
  funext k
  dsimp only [Function.comp_apply]
  rw [List.length_replicate]

lemma always_fails :
    Pr[RequestFails 0 | runROM (signingInteraction forbidden chooseForbidden)] = 1 := by
  rw [interaction]
  simp [runROM, romImpl, roSim.run_liftM, RequestFails, monad_norm]
  exact ENNReal.div_self (by norm_num) (by simp)

lemma requests : HasRequestBound chooseForbidden 1 := by
  intro pk
  exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

lemma hashes : HasInteractionHashBound forbidden chooseForbidden 0 := by
  rw [HasInteractionHashBound, interaction]
  rw [OracleComp.isQueryBoundP_map_iff]
  exact ⟨Or.inl (by decide), fun _ => trivial⟩

/-- The public-key-selected message defeats both new budget regimes. -/
theorem new_rejects (cap work : Nat) (hc : 1 ≤ cap) (hw : 1 ≤ work) :
    ¬ HasAdaptiveSigningFailureBound forbidden cap work 128 := by
  intro h
  have bad := h chooseForbidden 0 1 hc hw hashes requests 0 (by decide)
  rw [always_fails] at bad
  norm_num at bad

end LeanSphincsTest.AdaptiveAvailability
