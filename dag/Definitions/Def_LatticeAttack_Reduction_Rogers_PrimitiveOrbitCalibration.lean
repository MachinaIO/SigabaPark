module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelPrimitiveContent

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace SigabaNeo.Rogers

/-- Sum of the pushforwards of restricted Haar measure by primitive vector evaluation. -/
def primitiveOrbitMeasure {n : ℕ} (D : Set (SL n)) : Measure (E n) :=
  Measure.sum fun v : ContentFiber n 1 ↦ (groupHaar n |>.restrict D).map
    (fun g ↦ WithLp.toLp 2 (g • fun j ↦ (v.val.val j : ℝ)))

theorem primitiveOrbitMeasure_lintegral {n : ℕ} (D : Set (SL n))
    (u : E n → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ x, u x ∂primitiveOrbitMeasure D =
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val := by
  rw [primitiveOrbitMeasure, lintegral_sum_measure]
  apply tsum_congr
  intro v
  apply lintegral_map hu
  letI : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  change Continuous (fun g : SL n ↦ WithLp.toLp 2 (g.val.mulVec (fun j ↦ (v.val.val j : ℝ))))
  apply (PiLp.continuous_toLp 2 _).comp
  unfold Matrix.mulVec dotProduct
  fun_prop

/-- Unit-integral tests whose averaged workloads converge to the domain mass fix the scalar. -/
theorem primitiveOrbit_calibration {n : ℕ} {D : Set (SL n)} {C : ℝ≥0∞}
    (hC : primitiveOrbitMeasure D = C • volume)
    (f : ℕ → E n → ℝ≥0∞) (hf : ∀ j, Measurable (f j))
    (unit : ∀ j, ∫⁻ x, f j x = 1)
    (limit : Tendsto (fun j ↦ ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f j (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) atTop (𝓝 (groupHaar n D))) :
    (∀ u : E n → ℝ≥0∞, Measurable u →
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val = C * ∫⁻ x, u x) ∧
      C * ∑' k, dilationWeight n k = groupHaar n D := by
  have prim (u : E n → ℝ≥0∞) (hu : Measurable u) := primitiveOrbitMeasure_lintegral D u hu
  simp_rw [hC, lintegral_smul_measure, smul_eq_mul] at prim
  refine ⟨fun u hu ↦ (prim u hu).symm, ?_⟩
  have eqn (j : ℕ) : (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f j (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) = C * ∑' k, dilationWeight n k := by
    rw [siegel_integral_by_primitive D _ (hf j), ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← prim (fun x ↦ f j (((k + 1 : ℕ) : ℝ) • x)) ((hf j).comp (measurable_const_smul _)), lintegral_dilation k _ (hf j),
      unit j, mul_one]
  simp_rw [eqn] at limit
  exact tendsto_nhds_unique tendsto_const_nhds limit

#print axioms primitiveOrbit_calibration
end SigabaNeo.Rogers
