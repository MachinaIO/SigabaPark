import Mathlib
/-- Nearest-grid coefficient rounding and binary switching errors admit a uniform phase radius. -/
theorem solution (eps t : Fin 3 → ℝ) (e0 z P B : ℝ) (he0 : |e0| ≤ 1/2)
    (he : ∀ i, |eps i| ≤ 1/2) (ht : ∀ i, |t i| ≤ P) (hz : |z| ≤ B) :
    |(e0 + ∑ i, eps i * t i) + z| ≤ (1+3*P)/2 + B := by
  have hterm (i : Fin 3) : |eps i * t i| ≤ (1/2)*P := by
    rw [abs_mul]
    exact mul_le_mul (he i) (ht i) (abs_nonneg _) (by norm_num)
  have hs : |∑ i, eps i*t i| ≤ ∑ _i : Fin 3, (1/2:ℝ)*P :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
  simp at hs
  calc
    _ ≤ |e0 + ∑ i, eps i*t i| + |z| := abs_add_le _ _
    _ ≤ (|e0| + |∑ i, eps i*t i|) + |z| := by grw [abs_add_le e0]
    _ ≤ _ := by linarith
