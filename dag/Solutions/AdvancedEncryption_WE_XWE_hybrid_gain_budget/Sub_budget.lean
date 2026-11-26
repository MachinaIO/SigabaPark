import SigabaNeoStd

open Finset

theorem solution (m : ℕ) (p C : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hop : ∀ j < m, K * (p (j + 1) - p j) ^ 2 ≤ C j) :
    K * (p m - p 0) ^ 2 ≤ (m : ℝ) * ∑ j ∈ range m, C j := by
  let δ := fun j ↦ p (j + 1) - p j
  have ht : ∑ j ∈ range m, δ j = p m - p 0 := by
    dsimp [δ]
    exact sum_range_sub p m
  have hcs := sq_sum_le_card_mul_sum_sq (s := range m) (f := δ)
  rw [ht, card_range] at hcs
  calc
    _ ≤ K * (m * ∑ j ∈ range m, δ j ^ 2) := mul_le_mul_of_nonneg_left hcs hK
    _ = m * ∑ j ∈ range m, K * δ j ^ 2 := by rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun j hj ↦ hop j (mem_range.mp hj))
      (Nat.cast_nonneg m)
