import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

theorem AdvancedEncryption.WE.MaskedEval.otp_hop {E Y : Type*} [Fintype E] [Fintype Y]
    [AddCommGroup Y] (p : E → Y → ℝ) (g : E → Y → ℝ) (μ₀ μ₁ : Y) :
    |(∑ e, ∑ y, p e y * g e (y + μ₀)) - ∑ e, ∑ y, p e y * g e (y + μ₁)| ≤
      |(∑ e, ∑ y, p e y * g e (y + μ₀)) -
          ∑ e, (∑ y', p e y') * ((Fintype.card Y : ℝ)⁻¹ * ∑ y, g e (y + μ₀))| +
      |(∑ e, ∑ y, p e y * g e (y + μ₁)) -
          ∑ e, (∑ y', p e y') * ((Fintype.card Y : ℝ)⁻¹ * ∑ y, g e (y + μ₁))| := by sorry
