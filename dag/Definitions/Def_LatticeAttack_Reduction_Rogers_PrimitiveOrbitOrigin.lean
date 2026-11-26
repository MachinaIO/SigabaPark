module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

public section

open MeasureTheory
open scoped ENNReal

namespace SigabaNeo.Rogers

/-- Primitive integer vectors have nonzero image at every point of the Haar domain. -/
theorem primitiveOrbitMeasure_origin {n : ℕ} (D : Set (SL n)) :
    primitiveOrbitMeasure D {0} = 0 := by
  classical
  rw [primitiveOrbitMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  apply tsum_eq_zero_iff.mpr
  intro v
  let z := fun j ↦ (v.val.val j : ℝ)
  have hm : Measurable (fun g : SL n ↦ WithLp.toLp 2 (g • z)) := by
    let : BorelSpace (SL n) := ⟨rfl⟩
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous (fun g : SL n ↦ g.val.mulVec z)
    unfold Matrix.mulVec dotProduct
    fun_prop
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  suffices he : (fun g : SL n ↦ WithLp.toLp 2 (g • z)) ⁻¹' {0} = ∅ by rw [he, measure_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have h : g • z = (0 : Fin n → ℝ) := congrArg WithLp.ofLp
    (show WithLp.toLp 2 (g • z) = 0 from hg)
  have he : z = 0 := MulAction.injective g (h.trans (Matrix.mulVec_zero g.val).symm)
  exact v.val.property (funext fun i ↦ by
    have hi : (v.val.val i : ℝ) = 0 := congrFun he i
    exact_mod_cast hi)

#print axioms primitiveOrbitMeasure_origin

end SigabaNeo.Rogers
