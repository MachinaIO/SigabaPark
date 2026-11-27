import Mathlib
open scoped BigOperators

theorem AdvancedEncryption.WE.MaskedLookup.mixed_output_floor (agg ordinary : ℕ → ℕ → ℕ)
    (ab : ∀ s, 4*s ≤ agg 0 s) (ob : ∀ s, s ≤ ordinary 0 s)
    (aa : ∀ d s, agg d (agg d s) ≤ agg (d+1) s)
    (ao : ∀ d s, agg d (ordinary d s) ≤ ordinary (d+1) s)
    (d s : ℕ) : 4^(2^d-1)*s ≤ ordinary d s := by sorry
