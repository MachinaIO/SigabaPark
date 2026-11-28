import Mathlib

theorem AdvancedEncryption.WE.ResidualRelease.bad_header_hybrid {I : Type} [Fintype I] (p u : I → ℝ) (bad : I → Bool) (ε : ℝ)
    (nonneg : ∀ i, 0 ≤ p i) (total : ∑ i, p i = 1) (hε : 0 ≤ ε)
    (good : ∀ i, bad i = false → |u i| ≤ ε) (bound : ∀ i, |u i| ≤ 1) :
    |∑ i, p i * u i| ≤ ε + ∑ i, if bad i then p i else 0 := by sorry
