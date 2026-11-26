import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem solution {M b σ δ : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hσ : 0 < σ) (hrad : b ≤ σ * M)
    (hbudget : 6 * Real.pi * M ^ 2 * b ^ 2 ≤ δ * σ) :
    b * (2 * (Real.pi * M * (b ^ 2 + 2 * (σ * M) * b) / σ ^ 2)) ≤ δ := by
  have hsum : b ^ 2 + 2 * (σ * M) * b ≤ 3 * (σ * M) * b := by
    calc
      _ ≤ (σ * M) * b + 2 * (σ * M) * b := by
        exact add_le_add (by simpa [pow_two] using mul_le_mul_of_nonneg_right hrad hb) le_rfl
      _ = _ := by ring
  calc
    _ = (2 * b * (Real.pi * M) * (b ^ 2 + 2 * (σ * M) * b)) / σ ^ 2 := by ring
    _ ≤ (2 * b * (Real.pi * M) * (3 * (σ * M) * b)) / σ ^ 2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
        (sq_nonneg σ)
    _ ≤ δ := by
      apply (div_le_iff₀ (sq_pos_of_pos hσ)).2
      calc
        _ = (6 * Real.pi * M ^ 2 * b ^ 2) * σ := by ring
        _ ≤ (δ * σ) * σ := mul_le_mul_of_nonneg_right hbudget hσ.le
        _ = _ := by ring
