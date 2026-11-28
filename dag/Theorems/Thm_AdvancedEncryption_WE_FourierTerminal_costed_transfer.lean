import Mathlib

theorem AdvancedEncryption.WE.FourierTerminal.costed_transfer (gap keep win original wrapper evaluator : ℝ) (k h : ℕ)
    (hk : 0 < keep) (recovers : keep * gap^2 ≤ win)
    (hard : (2:ℝ)^h * win ≤ 2*evaluator + 1058 + wrapper)
    (budget : (2:ℝ)^k * (2*evaluator + 1058 + wrapper) ≤ (2:ℝ)^h * keep * original) :
    (2:ℝ)^k * gap^2 ≤ original := by
  sorry
