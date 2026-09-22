import Mathlib.Tactic

/-! Exact additive objective and historical experimental score arithmetic.
Not imported by the protected MVP Target.
Metrics still need certificates binding them to an actual scheme. -/

namespace LeanSphincs.OTS

structure Costs where
  signatureBytes : ℚ
  keygen : ℚ
  signing : ℚ
  verification : ℚ
deriving DecidableEq, Repr

def Costs.Positive (c : Costs) : Prop :=
  0 < c.signatureBytes ∧ 0 < c.keygen ∧ 0 < c.signing ∧ 0 < c.verification

/-- Historical objective only. For β = a/b, compare the b-th power of σ * S * V * K^β.
This avoids floating-point roots; it is not the current competition ranker.
Signing semantics (expected or worst-case) belong to the profile, not this formula. -/
def rankKey (a b : Nat) (c : Costs) : ℚ :=
  (c.signatureBytes * c.signing * c.verification) ^ b * c.keygen ^ a

def Costs.DominatedBy (c d : Costs) : Prop :=
  c.signatureBytes ≤ d.signatureBytes ∧ c.keygen ≤ d.keygen ∧
    c.signing ≤ d.signing ∧ c.verification ≤ d.verification

theorem rankKey_pos (a b : Nat) (c : Costs) (h : c.Positive) :
    0 < rankKey a b c := by
  rcases h with ⟨hs, hk, hg, hv⟩
  unfold rankKey
  positivity

/-- No Pareto-dominated metric vector can have a better rank key. -/
theorem rankKey_mono (a b : Nat) (c d : Costs) (hc : c.Positive)
    (h : c.DominatedBy d) : rankKey a b c ≤ rankKey a b d := by
  rcases hc with ⟨hs, hk, hg, hv⟩
  rcases h with ⟨hsd, hkd, hgd, hvd⟩
  have hds : 0 < d.signatureBytes := lt_of_lt_of_le hs hsd
  have hdg : 0 < d.signing := lt_of_lt_of_le hg hgd
  have hdv : 0 < d.verification := lt_of_lt_of_le hv hvd
  unfold rankKey
  gcongr

/-- Historical quarter-weight specialization, superseded by additive pricing. -/
theorem quarterKey (c : Costs) :
    rankKey 1 4 c = (c.signatureBytes * c.signing * c.verification)^4 * c.keygen := by
  simp [rankKey]

/-- Current objective. The positive bandwidth price is fixed by the organizer's
profile, not a submission. No production price has been calibrated yet. -/
def additiveScore (bandwidthPrice : ℚ) (c : Costs) : ℚ :=
  bandwidthPrice * c.signatureBytes + c.verification

theorem additiveScore_pos (price : ℚ) (c : Costs) (hp : 0 < price) (hc : c.Positive) :
    0 < additiveScore price c := by
  rcases hc with ⟨hs, hk, hg, hv⟩
  unfold additiveScore
  positivity

theorem additiveScore_mono (price : ℚ) (c d : Costs) (hp : 0 ≤ price)
    (hs : c.signatureBytes ≤ d.signatureBytes) (hv : c.verification ≤ d.verification) :
    additiveScore price c ≤ additiveScore price d := by
  unfold additiveScore
  gcongr

def stage1RankKey (price : ℚ) (c : Costs) : ℚ := additiveScore price c
def stage2RankKey (price : ℚ) (c : Costs) : ℚ := additiveScore price c

theorem stage2RankKey_eq_stage1 (price : ℚ) (c : Costs) :
    stage2RankKey price c = stage1RankKey price c := rfl

end LeanSphincs.OTS
