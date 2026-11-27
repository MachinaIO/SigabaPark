import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem AdvancedEncryption.WE.FEPacking.shard_capacity {A : Type} [Fintype A]
    (rows width : A → ℕ) (a b u : ℕ) (h : ∀ g, u ≤ width g) :
    2 * (∑ g, rows g) * a * b * u ≤
      ∑ g, b * (2 * (rows g * a) * width g) := by
  sorry
