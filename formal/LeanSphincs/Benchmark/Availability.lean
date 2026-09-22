import LeanSphincs.Benchmark.Game

/-! Adaptive availability uses one shared ROM and excludes final verification.
Positions are zero based. Probabilities are unconditional, including keygen and
participant randomness; an absent position is not a failed request. -/
open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Benchmark

structure SigningParticipant where
  main : Bytes → OracleComp (OracleWorld + SigningSpec) Unit

def signingInteraction (S : SigScheme) (A : SigningParticipant) :
    OracleComp OracleWorld (QueryLog SigningSpec) := do
  let (pk, sk) ← S.keygen
  let (_, log) ← (simulateQ (forwardOracles + signingOracle S sk) (A.main pk)).run
  return log

def RequestFails (i : Nat) (log : QueryLog SigningSpec) : Prop :=
  ∃ entry, log[i]? = some entry ∧ entry.2 = none

instance (i : Nat) (log : QueryLog SigningSpec) : Decidable (RequestFails i log) :=
  decidable_of_iff ((log[i]?).any (fun e => e.2.isNone) = true) (by
    simp [RequestFails, Option.any_eq_true, Option.isNone_iff_eq_none])

def HasInteractionHashBound (S : SigScheme) (A : SigningParticipant) (qH : Nat) : Prop :=
  (signingInteraction S A).IsQueryBoundP (· matches .inr _) qH

def HasRequestBound (A : SigningParticipant) (qS : Nat) : Prop :=
  ∀ pk, (A.main pk).IsQueryBoundP (· matches .inr _) qS

/-- Raw hashes include keygen, participant hashes and honest signing; requests
are additionally charged in qH + qS. Structural bounds cover every response path. -/
def HasAdaptiveSigningFailureBound (S : SigScheme) (cap work bits : Nat) : Prop :=
  ∀ (A : SigningParticipant) (qH qS : Nat), qS ≤ cap → qH + qS ≤ work →
    HasInteractionHashBound S A qH → HasRequestBound A qS → ∀ i, i < qS →
      Pr[RequestFails i | runROM (signingInteraction S A)] ≤ 1 / (2 : ℝ≥0∞) ^ bits

theorem HasAdaptiveSigningFailureBound.mono {S : SigScheme} {cap work weaker stronger : Nat}
    (h : HasAdaptiveSigningFailureBound S cap work stronger) (hle : weaker ≤ stronger) :
    HasAdaptiveSigningFailureBound S cap work weaker := by
  intro A qH qS hc hw hh hs i hi
  apply (h A qH qS hc hw hh hs i hi).trans
  simp only [one_div]
  exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) hle)

/-- Union bound for all permitted positions, with no independence assumption. -/
theorem HasAdaptiveSigningFailureBound.lifetime {S : SigScheme} {cap work bits : Nat}
    (h : HasAdaptiveSigningFailureBound S cap work bits)
    (A : SigningParticipant) (qH qS : Nat) (hc : qS ≤ cap) (hw : qH + qS ≤ work)
    (hh : HasInteractionHashBound S A qH) (hs : HasRequestBound A qS) :
    Pr[fun log => ∃ i ∈ Finset.range qS, RequestFails i log |
      runROM (signingInteraction S A)] ≤ (qS : ℝ≥0∞) / (2 : ℝ≥0∞) ^ bits := by
  apply (probEvent_exists_finset_le_sum (Finset.range qS) _ RequestFails).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range qS, 1 / (2 : ℝ≥0∞) ^ bits :=
      Finset.sum_le_sum fun i hi => h A qH qS hc hw hh hs i (Finset.mem_range.mp hi)
    _ = _ := by simp [div_eq_mul_inv]

/-- 2^32 requests at 128 bits give a 96-bit lifetime bound, not 128 bits. -/
theorem lifetime_32_value :
    ((2 ^ 32 : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 = 1 / (2 : ℝ≥0∞) ^ 96 := by
  rw [show 128 = 32 + 96 from rfl, pow_add]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_one] using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) ((2 : ℝ≥0∞) ^ 96)
    (c := (2 : ℝ≥0∞) ^ 32) (by norm_num) (by simp)

#guard RequestFails 0 [⟨0, none⟩, ⟨0, some []⟩, ⟨0, none⟩]
#guard ¬ RequestFails 1 [⟨0, none⟩, ⟨0, some []⟩, ⟨0, none⟩]
#guard RequestFails 2 [⟨0, none⟩, ⟨0, some []⟩, ⟨0, none⟩]
#guard ¬ RequestFails 3 [⟨0, none⟩, ⟨0, some []⟩, ⟨0, none⟩]
end LeanSphincs.Benchmark
