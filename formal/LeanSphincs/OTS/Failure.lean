import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Pow

/-! Adaptive signing-failure envelopes, not yet a certificate for a concrete signer.
The step premise must be proved from its actual ROM/cache experiment. It follows
from a success lower bound conditional on every surviving history; independence
of attempts is not required. A cached/adversarially fixed answer is not fresh.
This module must not be used to infer that premise from codebook size alone. -/

namespace LeanSphincs.OTS

/-- If each surviving step contracts failure mass by at most 1-p, the total
failure probability after attempts steps is at most (1-p)^attempts. -/
theorem failure_envelope (tail : Nat → ℝ) (p : ℝ) (hp : p ≤ 1)
    (initial : tail 0 ≤ 1)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - p)) (attempts : Nat) :
    tail attempts ≤ (1 - p)^attempts := by
  induction attempts with
  | zero => simpa using initial
  | succ n ih =>
    calc
      tail (n + 1) ≤ tail n * (1 - p) := step n
      _ ≤ (1 - p)^n * (1 - p) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ = (1 - p)^(n + 1) := by rw [pow_succ]

/-- An explicit allowance for exceptional/cached steps. Those allowances must
be bounded in the actual game; they cannot be silently discarded as fresh ROM
queries. This conservative version sums them without discounting. -/
theorem failure_envelope_with_exceptions (tail bad : Nat → ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (initial : tail 0 ≤ 1)
    (bad_nonneg : ∀ n, 0 ≤ bad n)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - p) + bad n) (attempts : Nat) :
    tail attempts ≤ (1 - p)^attempts + ∑ n ∈ Finset.range attempts, bad n := by
  induction attempts with
  | zero => simpa using initial
  | succ n ih =>
    have sum_nonneg : 0 ≤ ∑ k ∈ Finset.range n, bad k :=
      Finset.sum_nonneg (fun k _ => bad_nonneg k)
    have contraction := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 - p by linarith)
    have allowance : (∑ k ∈ Finset.range n, bad k) * (1 - p) ≤
        ∑ k ∈ Finset.range n, bad k := by nlinarith
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [step n]

/-- A conservative exact block bound: m*p ≥ 1 halves the survival mass. -/
theorem block_failure_le_half (p : ℝ) (m : Nat) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (budget : 1 ≤ (m : ℝ) * p) : (1 - p)^m ≤ 1 / 2 := by
  have hbase : 0 ≤ 1 - p := by linarith
  have bernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ p by linarith) m
  have growth : 2 ≤ (1 + p)^m := by linarith
  have contraction : ((1 - p) * (1 + p))^m ≤ (1 : ℝ)^m := by
    apply pow_le_pow_left₀ (mul_nonneg hbase (by linarith))
    nlinarith [sq_nonneg p]
  rw [mul_pow] at contraction
  have product := mul_le_mul_of_nonneg_left growth (pow_nonneg hbase m)
  norm_num at contraction
  linarith

/-- At p=2^-16, 65536*bits attempts suffice for a 2^-bits envelope. -/
theorem encoding_failure_bound (tail : Nat → ℝ) (bits : Nat)
    (initial : tail 0 ≤ 1)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - 1 / 65536)) :
    tail (65536 * bits) ≤ (1 / 2 : ℝ)^bits := by
  have geometric := failure_envelope tail (1 / 65536) (by norm_num) initial step (65536 * bits)
  have block : (1 - 1 / 65536 : ℝ)^65536 ≤ 1 / 2 :=
    block_failure_le_half _ _ (by norm_num) (by norm_num) (by norm_num)
  apply geometric.trans
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (by norm_num) _) block bits

end LeanSphincs.OTS
