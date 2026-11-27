import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution {A : Type} [Fintype A]
    (rows width : A → ℕ) (a b u : ℕ) (h : ∀ g, u ≤ width g) :
    2 * (∑ g, rows g) * a * b * u ≤
      ∑ g, b * (2 * (rows g * a) * width g) := by
  calc
    _ = (∑ g, rows g) * (2 * a * b * u) := by ring
    _ = ∑ g, rows g * (2 * a * b * u) := Finset.sum_mul ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro g _
      calc
        rows g * (2 * a * b * u) = (b * (2 * (rows g * a))) * u := by ring
        _ ≤ (b * (2 * (rows g * a))) * width g := Nat.mul_le_mul_left _ (h g)
        _ = _ := by ring
