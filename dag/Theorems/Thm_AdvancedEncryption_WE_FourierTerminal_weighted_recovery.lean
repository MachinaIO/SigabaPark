import Mathlib

theorem AdvancedEncryption.WE.FourierTerminal.weighted_recovery {I : Type} (s : Finset I) (w a success : I → ℝ) (wn : ∀ i ∈ s, 0 ≤ w i)
    (ws : ∑ i ∈ s, w i = 1) (ok : ∀ i ∈ s, a i ^ 2 ≤ success i) :
    (∑ i ∈ s, w i * a i)^2 ≤ ∑ i ∈ s, w i * success i := by
  sorry
