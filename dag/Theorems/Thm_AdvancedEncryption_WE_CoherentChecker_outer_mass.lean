import Mathlib

theorem AdvancedEncryption.WE.CoherentChecker.outer_mass {I : Type} (s : Finset I) (w a b : I → ℝ) (p : ℝ)
    (wn : ∀ i ∈ s, 0 ≤ w i) (left : ∑ i ∈ s, w i * a i^2 ≤ p)
    (right : ∑ i ∈ s, w i * b i^2 ≤ p) : ∑ i ∈ s, w i*(a i*b i) ≤ p := by
  sorry
