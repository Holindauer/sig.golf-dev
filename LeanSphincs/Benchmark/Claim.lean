import LeanSphincs.Benchmark.Availability
import LeanSphincs.Benchmark.Bound

/-! Protected pure-ROM claim with total query work and same-scheme lifetime decay.
Wallet/cycle budget clauses are not represented as completed gates. No conjectural
assumption, constants-dropping predicate or auxiliary cache interface is required. -/

namespace LeanSphincs.Benchmark

open ENNReal

def signingBudget : Nat := 2 ^ 20
def securityFloor : Nat := 124
def extendedSigningBudget : Nat := 2 ^ 32
def extendedSecurityFloor : Nat := 100
def signingFailureBits : Nat := 128

/-! Placeholder structural raw hash-query caps, uncalibrated. They bound every
structural path of the honest algorithms so that honest work
K + qS * (S + 1) + V stays inside both nontrivial security ranges; they do not
certify seconds. The values are chosen with generous headroom over a SPHINCS-scale
construction (keygen/sign/verify well under 2^28/2^20/2^16 hash calls) so that the
honest-work contribution to Q is small: at 2^20 requests it is about 2^40, and at
2^32 requests about 2^52, leaving the certified floor near 2^-84 and 2^-48 for a
zero-effort adversary rather than the vacuous slope a 2^128 pad would force.
Calibration against the reference execution profile is open, and these constants
must equal the raw-query caps mirrored in `benchmark/resources.json`. -/
def rawKeygenCap : Nat := 2 ^ 28
def rawSignCap : Nat := 2 ^ 20
def rawVerifyCap : Nat := 2 ^ 16

/-! Structural uniform-sampling caps, uncalibrated. Uniform draws are outside qH
and so do not affect the security floor, but bound working RAM and runtime. -/
def sampleKeygenCap : Nat := 2 ^ 28
def sampleSignCap : Nat := 2 ^ 20

noncomputable def boundProbability (coeffs : BoundCoeffs) (qW qS : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (evalBound coeffs qW qS : ℝ)

structure SchemeClaim (S : SigScheme) (sigmaBytes hVerify : Nat) (coeffs : BoundCoeffs) : Prop where
  correct : CorrectOnSuccess S
  signing_failure : HasSigningFailureBound S signingFailureBits
  adaptive_failure : HasAdaptiveSigningFailureBound S signingBudget (2 ^ securityFloor) signingFailureBits
  adaptive_decay_failure : HasAdaptiveSigningFailureBound S extendedSigningBudget
    (2 ^ extendedSecurityFloor) signingFailureBits
  sigma_positive : 0 < sigmaBytes
  sigma_size : HasSignatureSize S sigmaBytes
  public_key_size : HasPublicKeySize S 32
  hverify_positive : 0 < hVerify
  verify_queries : HasVerificationBound S hVerify
  keygen_queries : HasKeygenQueryBound S rawKeygenCap
  sign_queries : HasSignQueryBound S rawSignCap
  verify_raw_queries : HasVerifyQueryBound S rawVerifyCap
  keygen_samples : HasKeygenSampleBound S sampleKeygenCap
  sign_samples : HasSignSampleBound S sampleSignCap
  security : ∀ (A : Adversary) (qH qS : Nat), qS ≤ extendedSigningBudget →
    HasHashQueryBound S A qH → HasSigningQueryBound A qS →
      sufAdvantage S A ≤ boundProbability coeffs (qH + qS) qS
  floor : MeetsFloor coeffs signingBudget securityFloor
  decay_floor : MeetsFloor coeffs extendedSigningBudget extendedSecurityFloor

/-- Honest structural work K + qS * (S + 1) + V is far below both security
ranges, so the whole-experiment budget cannot be padded into vacuity. -/
theorem honestWork_lt_floor :
    rawKeygenCap + signingBudget * (rawSignCap + 1) + rawVerifyCap < 2 ^ securityFloor := by
  decide

theorem honestWork_lt_decay_floor :
    rawKeygenCap + extendedSigningBudget * (rawSignCap + 1) + rawVerifyCap <
      2 ^ extendedSecurityFloor := by
  decide

private theorem SchemeClaim.at_floor {S : SigScheme} {sigma hverify : Nat} {coeffs : BoundCoeffs}
    (claim : SchemeClaim S sigma hverify coeffs) (cap bits : Nat)
    (hcap : cap ≤ extendedSigningBudget) (hf : MeetsFloor coeffs cap bits)
    (A : Adversary) (qH qS : Nat) (hSmax : qS ≤ cap)
    (hlo : 1 ≤ qH + qS) (hhi : qH + qS ≤ 2 ^ bits)
    (hH : HasHashQueryBound S A qH) (hS : HasSigningQueryBound A qS) :
    sufAdvantage S A ≤ ((qH + qS : Nat) : ℝ≥0∞) / 2 ^ bits := by
  have hq : evalBound coeffs ((qH + qS : Nat) : ℚ) qS ≤ ((qH + qS : Nat) : ℚ) / 2 ^ bits :=
    (evalBound_mono_signing coeffs (qW := ((qH + qS : Nat) : ℚ)) (by positivity) hSmax).trans
      (hf.sound (qW := ((qH + qS : Nat) : ℚ)) (by exact_mod_cast hlo) (by exact_mod_cast hhi))
  have hr : (evalBound coeffs ((qH + qS : Nat) : ℚ) qS : ℝ) ≤ ((qH + qS : Nat) : ℝ) / 2 ^ bits := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using hc
  apply (claim.security A qH qS (hSmax.trans hcap) hH hS).trans
  have := ENNReal.ofReal_le_ofReal hr
  simpa only [boundProbability,
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ bits),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat] using this

/-- The normal-lifetime floor is measured against total work qH + qS. -/
theorem SchemeClaim.security_le {S : SigScheme} {sigma hverify : Nat} {coeffs : BoundCoeffs}
    (claim : SchemeClaim S sigma hverify coeffs) (A : Adversary) (qH qS : Nat)
    (hSmax : qS ≤ signingBudget) (hlo : 1 ≤ qH + qS)
    (hhi : qH + qS ≤ 2 ^ securityFloor)
    (hH : HasHashQueryBound S A qH) (hS : HasSigningQueryBound A qS) :
    sufAdvantage S A ≤ ((qH + qS : Nat) : ℝ≥0∞) / 2 ^ securityFloor :=
  claim.at_floor signingBudget securityFloor (by decide) claim.floor A qH qS hSmax hlo hhi hH hS

/-- The same S and coefficients, not a reparameterized scheme, at 2^32 requests. -/
theorem SchemeClaim.decay_le {S : SigScheme} {sigma hverify : Nat} {coeffs : BoundCoeffs}
    (claim : SchemeClaim S sigma hverify coeffs) (A : Adversary) (qH qS : Nat)
    (hSmax : qS ≤ extendedSigningBudget) (hlo : 1 ≤ qH + qS)
    (hhi : qH + qS ≤ 2 ^ extendedSecurityFloor)
    (hH : HasHashQueryBound S A qH) (hS : HasSigningQueryBound A qS) :
    sufAdvantage S A ≤ ((qH + qS : Nat) : ℝ≥0∞) / 2 ^ extendedSecurityFloor :=
  claim.at_floor extendedSigningBudget extendedSecurityFloor le_rfl claim.decay_floor
    A qH qS hSmax hlo hhi hH hS

end LeanSphincs.Benchmark
