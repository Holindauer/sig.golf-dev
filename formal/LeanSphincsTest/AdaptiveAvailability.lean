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
  split_ifs <;> simp_all

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

/-- Always-successful toy signer: no unforgeability claim. -/
def available : SigScheme where
  SecretKey := Unit
  keygen := pure ([], ())
  sign := fun _ _ => pure (some [])
  verify := fun _ _ _ => pure true

lemma successful_log (comp : OracleComp (OracleWorld + SigningSpec) Unit) :
    ∀ result ∈ support ((simulateQ (forwardOracles + signingOracle available ()) comp).run),
      ∀ entry ∈ result.2, entry.2 ≠ none := by
  induction comp using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    cases t with
    | inl t =>
      simp [forwardOracles, monad_norm, support_bind]
      intro log u initialLog hu x tail ht hl entry he
      change (u, initialLog) ∈ support ((fun value => (value, [])) <$>
        (liftM (OracleWorld.query t) : OracleComp OracleWorld _)) at hu
      have empty : initialLog = [] := by simpa using hu
      subst initialLog
      simp only [List.nil_append] at hl
      subst log
      exact ih u (x, tail) ht entry he
    | inr message =>
      simp [signingOracle, available, QueryImpl.withLogging, QueryImpl.withTraceAppend,
        monad_norm, support_bind]
      intro log x tail ht hl entry he
      subst log
      rcases List.mem_cons.mp he with he | he
      · subst entry; simp
      · exact ih (some []) (x, tail) ht entry he

theorem positive_certificate (cap work bits : Nat) :
    HasAdaptiveSigningFailureBound available cap work bits := by
  intro A qH qS hc hw hh hs i hi
  have zero : Pr[RequestFails i | runROM (signingInteraction available A)] = 0 := by
    rw [probEvent_eq_zero_iff]
    intro log hlog
    have hsupport := support_simulateQ_run'_subset romImpl (signingInteraction available A) ∅ hlog
    simp only [signingInteraction, available, pure_bind] at hsupport
    simp only [support_bind, support_pure, Set.mem_iUnion, exists_prop,
      Set.mem_singleton_iff] at hsupport
    obtain ⟨result, hr, rfl⟩ := hsupport
    rintro ⟨entry, he, hn⟩
    exact successful_log (A.main []) result hr entry (List.mem_of_getElem? he) hn
  rw [zero]
  exact zero_le

example : HasAdaptiveSigningFailureBound available signingBudget (2 ^ securityFloor) 128 :=
  positive_certificate _ _ _
example : HasAdaptiveSigningFailureBound available extendedSigningBudget
    (2 ^ extendedSecurityFloor) 128 := positive_certificate _ _ _

example : HasSigningFailureBound forbidden signingFailureBits :=
  old_certificate.mono (by decide)

example : ¬ HasAdaptiveSigningFailureBound forbidden signingBudget
    (2 ^ securityFloor) signingFailureBits := new_rejects _ _ (by decide) (by decide)
example : ¬ HasAdaptiveSigningFailureBound forbidden extendedSigningBudget
    (2 ^ extendedSecurityFloor) signingFailureBits := new_rejects _ _ (by decide) (by decide)

example (S : SigScheme) (cap work : Nat)
    (h : HasAdaptiveSigningFailureBound S cap work 256) :
    HasAdaptiveSigningFailureBound S cap work signingFailureBits := h.mono (by decide)

/-- Apply the union bound to a full strengthened claim, allowing fewer requests. -/
theorem claim_lifetime {S : SigScheme} {sigma hverify : Nat} {coeffs : BoundCoeffs}
    (claim : SchemeClaim S sigma hverify coeffs) (A : SigningParticipant) (qH qS : Nat)
    (hc : qS ≤ extendedSigningBudget) (hw : qH + qS ≤ 2 ^ extendedSecurityFloor)
    (hh : HasInteractionHashBound S A qH) (hs : HasRequestBound A qS) :
    Pr[fun log => ∃ i ∈ Finset.range qS, RequestFails i log |
      runROM (signingInteraction S A)] ≤ 1 / (2 : ℝ≥0∞) ^ 96 := by
  apply (claim.adaptive_decay_failure.lifetime A qH qS hc hw hh hs).trans
  calc
    (qS : ℝ≥0∞) / (2 : ℝ≥0∞) ^ signingFailureBits ≤
        (extendedSigningBudget : ℝ≥0∞) / (2 : ℝ≥0∞) ^ signingFailureBits := by
      exact ENNReal.div_le_div_right (by exact_mod_cast hc) _
    _ = _ := lifetime_32_value

def repeated : SigningParticipant where
  main := fun _ => do
    let _ ← (OracleWorld + SigningSpec).query (.inr 0)
    let _ ← (OracleWorld + SigningSpec).query (.inr 0)
    pure ()

def failing : SigScheme := { available with sign := fun _ _ => pure none }

example : signingInteraction available repeated = pure [⟨0, some []⟩, ⟨0, some []⟩] := by
  simp [signingInteraction, available, repeated, signingOracle,
    QueryImpl.withLogging, QueryImpl.withTraceAppend, monad_norm]

example : signingInteraction failing repeated = pure [⟨0, none⟩, ⟨0, none⟩] := by
  simp [signingInteraction, failing, available, repeated, signingOracle,
    QueryImpl.withLogging, QueryImpl.withTraceAppend, monad_norm]

example : HasRequestBound repeated 2 := by
  intro pk
  exact ⟨Or.inr (by decide), fun _ => ⟨Or.inr (by decide), fun _ => trivial⟩⟩

example : ¬ HasRequestBound repeated 1 := by
  intro h
  exact ((h []).2 none).1.elim (fun hnp => hnp rfl) (Nat.not_lt_zero _)

example (i : Nat) : ¬ RequestFails i [] := by simp [RequestFails]

end LeanSphincsTest.AdaptiveAvailability
