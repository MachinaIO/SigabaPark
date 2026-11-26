import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution {E Y : Type*} [Fintype E] [Fintype Y]
    [AddCommGroup Y] (p : E → Y → ℝ) (g : E → Y → ℝ) (μ₀ μ₁ : Y) :
    |(∑ e, ∑ y, p e y * g e (y + μ₀)) - ∑ e, ∑ y, p e y * g e (y + μ₁)| ≤
      |(∑ e, ∑ y, p e y * g e (y + μ₀)) -
          ∑ e, (∑ y', p e y') * ((Fintype.card Y : ℝ)⁻¹ * ∑ y, g e (y + μ₀))| +
      |(∑ e, ∑ y, p e y * g e (y + μ₁)) -
          ∑ e, (∑ y', p e y') * ((Fintype.card Y : ℝ)⁻¹ * ∑ y, g e (y + μ₁))| := by
  have hshift : ∀ (e : E) (μ : Y), ∑ y, g e (y + μ) = ∑ y, g e y := fun e μ =>
    Fintype.sum_equiv (Equiv.addRight μ) _ _ (fun _ => rfl)
  simp only [hshift]
  set I := ∑ e, (∑ y', p e y') * ((Fintype.card Y : ℝ)⁻¹ * ∑ y, g e y)
  calc _ = |((∑ e, ∑ y, p e y * g e (y + μ₀)) - I) -
            ((∑ e, ∑ y, p e y * g e (y + μ₁)) - I)| := by ring_nf
    _ ≤ _ := abs_sub _ _
