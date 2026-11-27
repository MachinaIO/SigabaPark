module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SigabaNeo.Rogers

def densityBall (n j : ℕ) := Metric.ball (0 : E n) ((j : ℝ) + 1)

def densityTest (n j : ℕ) : E n → ℝ≥0∞ :=
  (densityBall n j).indicator (fun _ ↦ (volume (densityBall n j))⁻¹)

theorem densityTest_measurable (n j : ℕ) : Measurable (densityTest n j) :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet

theorem densityTest_unit (n j : ℕ) : ∫⁻ x, densityTest n j x = 1 := by
  rw [densityTest, densityBall, lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  apply ENNReal.inv_mul_cancel
  · exact (Metric.measure_ball_pos volume _ (by positivity : 0 < (j : ℝ) + 1)).ne'
  · exact measure_ball_lt_top.ne

def densityWork (n j : ℕ) (g : SL n) : ℝ≥0∞ :=
  tupleWorkload (fun v : Fin 1 → E n ↦ densityTest n j (v 0)) (QuotientGroup.mk g)

theorem densityTest_limit_of_bound (n : ℕ) (D : Set (SL n))
    (pointwise : ∀ g : SL n, Tendsto (fun j ↦ densityWork n j g) atTop (𝓝 1))
    (majorant : ∃ b : SL n → ℝ≥0∞, (∫⁻ g in D, b g ∂groupHaar n) ≠ ⊤ ∧
      ∀ j, densityWork n j ≤ᵐ[(groupHaar n).restrict D] b) :
    Tendsto (fun j ↦ ∫⁻ g in D, densityWork n j g ∂groupHaar n) atTop (𝓝 (groupHaar n D)) := by
  obtain ⟨b, hb, hle⟩ := majorant
  have hm (j : ℕ) : Measurable (densityWork n j) :=
    (tupleWorkload_measurable ((densityTest_measurable n j).comp (measurable_pi_apply 0))).comp
      measurable_quotient_mk''
  simpa using tendsto_lintegral_of_dominated_convergence (f := fun _ ↦ 1) b hm hle hb
    (Filter.Eventually.of_forall pointwise)

end SigabaNeo.Rogers
