import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem solution (adv eps cost sim : ℝ) (D k h : ℕ)
    (hadv : |adv| ≤ (2 * D : ℝ) * eps)
    (hstep : (2 : ℝ)^h * eps^2 ≤ sim)
    (hbudget : (2 : ℝ)^k * (2 * D : ℝ)^2 * sim ≤ (2 : ℝ)^h * cost) :
    (2 : ℝ)^k * adv^2 ≤ cost := by
  have he : 0 ≤ (2 * D : ℝ) * eps := (abs_nonneg _).trans hadv
  have hs := mul_self_le_mul_self (abs_nonneg _) hadv
  rw [← sq, sq_abs] at hs
  have hsq : adv^2 ≤ (2 * D : ℝ)^2 * eps^2 := by nlinarith only [hs]
  have hscaled := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (2:ℝ)^k*(2*D:ℝ)^2 by positivity)
  have combined : (2:ℝ)^h * ((2:ℝ)^k*adv^2) ≤ (2:ℝ)^h * cost := calc
    _ ≤ (2:ℝ)^h * ((2:ℝ)^k*((2*D:ℝ)^2*eps^2)) := by gcongr
    _ = ((2:ℝ)^k*(2*D:ℝ)^2)*((2:ℝ)^h*eps^2) := by ring
    _ ≤ _ := hscaled.trans hbudget
  exact le_of_mul_le_mul_left combined (by positivity)
