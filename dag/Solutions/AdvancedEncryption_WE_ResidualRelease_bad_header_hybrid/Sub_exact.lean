import Mathlib

theorem solution {I : Type} [Fintype I] (p u : I → ℝ) (bad : I → Bool) (ε : ℝ)
    (nonneg : ∀ i, 0 ≤ p i) (total : ∑ i, p i = 1) (hε : 0 ≤ ε)
    (good : ∀ i, bad i = false → |u i| ≤ ε) (bound : ∀ i, |u i| ≤ 1) :
    |∑ i, p i * u i| ≤ ε + ∑ i, if bad i then p i else 0 := by
  classical
  calc
    _ ≤ ∑ i, |p i * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (p i * ε + (if bad i then p i else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (nonneg i)]
      cases h : bad i with
      | false => simpa using mul_le_mul_of_nonneg_left (good i h) (nonneg i)
      | true =>
        simp only [Bool.true_eq,if_true]
        have hh := mul_le_mul_of_nonneg_left (bound i) (nonneg i)
        nlinarith [mul_nonneg (nonneg i) hε]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, total, one_mul]
