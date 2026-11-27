import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

theorem solution (levels n m q : ℕ) (σ : ℝ) (hn : 1 ≤ n) (hm : 5 * n ≤ m)
    (hshort : 1 ≤ Real.sqrt m * σ)
    (hcorrect : ((m : ℝ) ^ 2 * σ) ^ (4 * levels) ≤ q)
    (hmod : (q : ℝ) ≤ (2 : ℝ) ^ Real.sqrt n) :
    12 * (levels : ℝ) ≤ Real.logb 2 q ∧ (12 * levels) ^ 2 ≤ n := by
  have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast (show 5 ≤ m by omega)
  have hs2 : 2 ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by linarith)
  have hh : 2 ≤ (m : ℝ) * σ := calc
    (2 : ℝ) = 2 * 1 := by ring
    _ ≤ Real.sqrt m * (Real.sqrt m * σ) := mul_le_mul hs2 hshort (by norm_num) (by positivity)
    _ = m * σ := by rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]
  have h8 : 8 ≤ (m : ℝ) ^ 2 * σ := calc
    (8 : ℝ) ≤ 5 * 2 := by norm_num
    _ ≤ (m : ℝ) * (m * σ) := mul_le_mul hm5 hh (by norm_num) (by positivity)
    _ = _ := by ring
  have hp : (8 : ℝ) ^ (4 * levels) ≤ q :=
    (pow_le_pow_left₀ (by norm_num) h8 _).trans hcorrect
  have hu := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hp
  have h8log : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [Real.logb_pow, h8log] at hu
  push_cast at hu
  have hlo : 12 * (levels : ℝ) ≤ Real.logb 2 q := by linarith
  have hq : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hp
  have hhi := Real.logb_le_logb_of_le (b := 2) (by norm_num) hq hmod
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hhi
  have hdim : (12 * (levels : ℝ)) ^ 2 ≤ n :=
    (Real.le_sqrt (by positivity) (by positivity)).mp (hlo.trans hhi)
  exact ⟨hlo, by exact_mod_cast hdim⟩
