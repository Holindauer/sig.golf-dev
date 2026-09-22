import LeanSphincs.OTS.Failure

open LeanSphincs.OTS

example (tail : Nat → ℝ) (initial : tail 0 ≤ 1)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - 1 / 65536)) :
    tail 8388608 ≤ (1 / 2 : ℝ)^128 := encoding_failure_bound tail 128 initial step

example (tail : Nat → ℝ) (initial : tail 0 ≤ 1)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - 1 / 65536)) :
    tail 16777216 ≤ (1 / 2 : ℝ)^256 := encoding_failure_bound tail 256 initial step

/-- An always-failing process cannot satisfy the positive-success step premise. -/
example : ¬ (∀ _n : Nat, (1 : ℚ) ≤ 1 * (1 - 1 / 65536)) := by norm_num

/-- A lifetime 128-bit failure target across 2^20 requests would require a
stronger per-request allowance, not reuse of the 128-bit single-request gate. -/
example : (2 : ℚ)^20 * (1 / 2 : ℚ)^148 = (1 / 2 : ℚ)^128 := by norm_num

example : 65536 * 148 = (9699328 : Nat) := by decide
example : 3 * 8388608 = (25165824 : Nat) := by decide

example : (2 : ℚ)^20 * (1 / 2 : ℚ)^128 = (1 / 2 : ℚ)^108 := by norm_num

example : (1 / 2 : ℚ)^129 + (1 / 2 : ℚ)^129 = (1 / 2 : ℚ)^128 := by norm_num

example (tail : Nat → ℝ) (initial : tail 0 ≤ 1)
    (step : ∀ n, tail (n + 1) ≤ tail n * (1 - 1 / 65536) + 0) (n : Nat) :
    tail n ≤ (1 - 1 / 65536)^n := by
  simpa using failure_envelope_with_exceptions tail (fun _ => 0) (1 / 65536)
    (by norm_num) (by norm_num) initial (by intro; norm_num) step n
