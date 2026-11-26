module

public import Mathlib
import all Definitions.Def_LatticeAttack_Research_Wall1_PlanarHermite

set_option autoImplicit true

public section
namespace SigabaNeo.Wall1.ControlledPlane
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Binary Hermite applied in the intrinsic span of an arbitrary independent pair. -/
theorem short_in_span (vct : Fin 2 → V) (hi : LinearIndependent ℝ vct) :
    ∃ v ∈ Submodule.span ℤ (Set.range vct), v ≠ 0 ∧
      Real.sqrt 3 * ‖v‖^2 ≤ 2 * Real.sqrt (Matrix.gram ℝ vct).det := by
  let D := Real.sqrt (Matrix.gram ℝ vct).det
  have hp := (Matrix.posDef_gram_of_linearIndependent hi).det_pos
  obtain ⟨c,d,hcd,h⟩ := binary_short (‖vct 0‖^2) ⟪vct 0,vct 1⟫ (‖vct 1‖^2) D
    (sq_pos_of_pos (norm_pos_iff.mpr (hi.ne_zero 0))) (Real.sqrt_pos.mpr hp) (by
      dsimp only [D]; rw [Real.sq_sqrt hp.le, Matrix.det_fin_two]
      simp only [Matrix.gram_apply, real_inner_self_eq_norm_sq, real_inner_comm (vct 1) (vct 0)]
      ring)
  let v := c • vct 1 + d • vct 0
  refine ⟨v, Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
    (Set.mem_range_self 1))) (Submodule.smul_mem _ _ (Submodule.subset_span
    (Set.mem_range_self 0))), ?_, ?_⟩
  · intro hv
    have hh : ∑ i, (![d,c] i : ℤ) • vct i = 0 := by
      simpa [Fin.sum_univ_two, v, add_comm] using hv
    have hi := Fintype.linearIndependent_iff.mp (hi.restrict_scalars' ℤ) ![d,c] hh
    rcases hcd with hc | hd
    · exact hc (hi 1)
    · exact hd (hi 0)
  · have eq : ‖v‖^2 = ‖vct 1‖^2*c^2 + 2*⟪vct 0,vct 1⟫*c*d + ‖vct 0‖^2*d^2 := by
      simp only [v, ← Int.cast_smul_eq_zsmul ℝ, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right, real_inner_comm (vct 1)
        (vct 0)]
      ring
    rw [eq]
    exact h

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.short_in_span
