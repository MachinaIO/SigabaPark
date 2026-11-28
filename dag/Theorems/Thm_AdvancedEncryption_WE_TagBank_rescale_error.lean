import Mathlib
/-- Nearest-grid coefficient rounding and binary switching errors admit a uniform phase radius. -/
theorem AdvancedEncryption.WE.TagBank.rescale_error (eps t : Fin 3 → ℝ) (e0 z P B : ℝ) (he0 : |e0| ≤ 1/2)
    (he : ∀ i, |eps i| ≤ 1/2) (ht : ∀ i, |t i| ≤ P) (hz : |z| ≤ B) :
    |(e0 + ∑ i, eps i * t i) + z| ≤ (1+3*P)/2 + B := by sorry
