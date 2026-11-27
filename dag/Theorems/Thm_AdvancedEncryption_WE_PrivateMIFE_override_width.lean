import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.override_width (child seed : ℕ)
    (pack : (Fin child → Bool) → (Fin seed → Bool))
    (run : (Fin seed → Bool) → (Fin child → Bool))
    (fallback : ∀ u, run (pack u) = u) : child ≤ seed := by sorry
