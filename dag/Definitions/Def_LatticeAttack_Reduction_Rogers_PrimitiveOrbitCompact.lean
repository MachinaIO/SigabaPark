import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests

set_option autoImplicit true

open MeasureTheory
open scoped ENNReal

namespace SigabaNeo.Rogers

/-- The content-one term is bounded by the full normalized count. Finiteness of each
averaged ball count therefore gives finiteness on arbitrary compact sets. -/
theorem primitiveOrbitCompact_of_densityWork {n : ℕ} (D : Set (SL n))
    (finite : ∀ j, (∫⁻ g in D, densityWork n j g ∂groupHaar n) ≠ ⊤) :
    IsFiniteMeasureOnCompacts (primitiveOrbitMeasure D) := by
  constructor
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball 0
  obtain ⟨j, hj⟩ := exists_nat_gt r
  have sub : K ⊆ densityBall n j := hr.trans (Metric.ball_subset_ball (by linarith))
  apply measure_lt_top_of_subset sub
  have bound : (∫⁻ x, densityTest n j x ∂primitiveOrbitMeasure D) ≤
      ∫⁻ g in D, densityWork n j g ∂groupHaar n := by
    rw [primitiveOrbitMeasure_lintegral D _ (densityTest_measurable n j)]
    unfold densityWork
    rw [siegel_integral_by_primitive D _ (densityTest_measurable n j)]
    simpa using (le_tsum (fun k : ℕ ↦ ∑' v : ContentFiber n 1,
      vectorOrbitalIntegral D (fun x ↦ densityTest n j (((k + 1 : ℕ) : ℝ) • x)) v.val) 0)
  have fin := ne_top_of_le_ne_top (finite j) bound
  rw [densityTest, lintegral_indicator (show MeasurableSet (densityBall n j) from Metric.isOpen_ball.measurableSet), setLIntegral_const] at fin
  intro h
  apply fin
  rw [h, ENNReal.mul_top]
  simp [densityBall, measure_ball_lt_top.ne]

#print axioms primitiveOrbitCompact_of_densityWork

end SigabaNeo.Rogers
