import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem AdvancedEncryption.WE.Rectangle.transfer (adv eps cost sim : ℝ) (D k h : ℕ)
    (hadv : |adv| ≤ (2 * D : ℝ) * eps)
    (hstep : (2 : ℝ)^h * eps^2 ≤ sim)
    (hbudget : (2 : ℝ)^k * (2 * D : ℝ)^2 * sim ≤ (2 : ℝ)^h * cost) :
    (2 : ℝ)^k * adv^2 ≤ cost := by sorry
