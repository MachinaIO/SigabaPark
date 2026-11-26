import Mathlib

open Finset
open scoped BigOperators

theorem solution {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ) (v : I → ℤ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) :
    (∑ j, (∑ i, v i * A i j)^2) ≤
      ∑ j, (max (∑ i, max (A i j) 0) (∑ i, max (-A i j) 0))^2 := by
  apply sum_le_sum
  intro j _
  let b := max (∑ i, max (A i j) 0) (∑ i, max (-A i j) 0)
  have hu : (∑ i, v i * A i j) ≤ b := by
    apply le_trans _ (le_max_left ..)
    apply sum_le_sum
    intro i _
    rcases hv i with h | h <;> simp [h]
  have hl : -(∑ i, v i * A i j) ≤ b := by
    rw [← sum_neg_distrib]
    apply le_trans _ (le_max_right ..)
    apply sum_le_sum
    intro i _
    rcases hv i with h | h <;> simp [h]
  change _ ≤ b^2
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ b + ∑ i, v i * A i j by omega)]
