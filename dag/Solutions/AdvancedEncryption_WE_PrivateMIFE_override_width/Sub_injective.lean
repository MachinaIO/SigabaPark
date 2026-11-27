import Mathlib

theorem solution (child seed : ℕ)
    (pack : (Fin child → Bool) → (Fin seed → Bool))
    (run : (Fin seed → Bool) → (Fin child → Bool))
    (fallback : ∀ u, run (pack u) = u) : child ≤ seed := by
  have hi : Function.Injective pack := Function.LeftInverse.injective fallback
  have hc := Fintype.card_le_of_injective pack hi
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
