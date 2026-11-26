module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

@[expose] public section
noncomputable section

open MeasureTheory
namespace SigabaNeo.Rogers

/-- Coordinate patches cover the complement of the axis, and translation preserves each patch. -/
theorem axisComplementTranslation_of_patches {n : ℕ} (μ : Measure (E n)) (i : Fin n) (t : ℝ)
    (h : ∀ j : Fin n, j ≠ i →
      (μ.map (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·)).restrict {x | x j ≠ 0} =
        μ.restrict {x | x j ≠ 0}) :
    (μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ).map
      (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·) =
      μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ := by
  classical
  let e := MeasurableEquiv.addLeft (t • EuclideanSpace.basisFun (Fin n) ℝ i)
  let U := {x : E n | ∀ j ≠ i, x j = 0}ᶜ
  have cover : U = ⋃ j : {j : Fin n // j ≠ i}, {x : E n | x j ≠ 0} := by
    ext x
    simp [U]
  have pre : e ⁻¹' U = U := by
    ext x
    change (¬ ∀ j ≠ i, (t • EuclideanSpace.basisFun (Fin n) ℝ i + x) j = 0) ↔ _
    simp +contextual [U, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply]
  change (μ.restrict U).map e = μ.restrict U
  rw [← pre, ← e.restrict_map, pre, cover, Measure.restrict_iUnion_congr]
  exact fun j ↦ h j j.property

end SigabaNeo.Rogers
