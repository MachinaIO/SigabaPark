import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem AdvancedEncryption.WE.LeafView.floodingWidth_jointTheta {M b σ δ : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hσ : 0 < σ) (hrad : b ≤ σ * M)
    (hbudget : 6 * Real.pi * M ^ 2 * b ^ 2 ≤ δ * σ) :
    b * (2 * (Real.pi * M * (b ^ 2 + 2 * (σ * M) * b) / σ ^ 2)) ≤ δ := by
  sorry
