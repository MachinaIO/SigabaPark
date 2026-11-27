import Definitions.Def_LatticeAttack_Reduction_Rogers_CoordinatePatchTranslations
import Definitions.Def_LatticeAttack_Reduction_Rogers_DensityUnitMajorant
import Definitions.Def_LatticeAttack_Reduction_Rogers_MeanValue
import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration
import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCompact
import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitInvariance
import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitOrigin
import Definitions.Def_LatticeAttack_Reduction_Rogers_ResidueBallBound
import Definitions.Def_LatticeAttack_Reduction_Rogers_SLCoordinateAxisNull
import Definitions.Def_LatticeAttack_Reduction_Rogers_SLPatchShears
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyDomain
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelBallPointwise
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelPrimitiveContent
import Definitions.Def_LatticeAttack_Reduction_Rogers_UnitBallQRCount
import Definitions.Def_LatticeAttack_Reduction_Rogers_UnitBallQRIntegral

set_option autoImplicit true

open MeasureTheory Filter
open scoped ENNReal Topology Pointwise

namespace SigabaNeo.Rogers

theorem siegel_positive_dilations_of_primitive_vectors {n : ℕ} (D : Set (SL n)) (C : ℝ≥0∞)
    (prim : ∀ (u : E n → ℝ≥0∞), Measurable u →
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val = C * ∫⁻ x, u x)
    (mass : C * ∑' k, dilationWeight n k = groupHaar n D)
    (f : E n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) = groupHaar n D * ∫⁻ x, f x := siegel_of_primitive_constant D C prim mass f hf

theorem primitive_orbit_sl_invariance (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) : ∀ g
    : SL n, Measure.map (fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)) (primitiveOrbitMeasure D)
    = primitiveOrbitMeasure D := primitiveOrbitMeasure_sl_invariant hd

theorem primitive_orbit_compact_of_finite_density_work : type_of%
    @primitiveOrbitCompact_of_densityWork := @primitiveOrbitCompact_of_densityWork

theorem siegel_density_unit_ball_integral_finite (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm :
    MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin :
    groupHaar n D ≠ ⊤) : (∫⁻ g in D, densityWork n 0 g ∂groupHaar n) ≠ ⊤ := by
  cases n with
  | zero => omega
  | succ d =>
    have hp : 1 ≤ d := by omega
    exact ne_top_of_le_ne_top (unit_ball_qr_product_siegel_integrable d hp)
      ((densityWork_domain_le_cover 0 hd (column_siegel_arithmetic_cover d hp)).trans
        (lintegral_mono (unit_ball_work_le_qr_product d hp)))

theorem siegel_density_ball_majorant (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) : ∃ b
    : SL n → ℝ≥0∞, (∫⁻ g in D, b g ∂groupHaar n) ≠ ⊤ ∧ ∀ j, densityWork n j ≤ᵐ[(groupHaar
    n).restrict D] b := by
  exact densityMajorant_of_unitComparison n D hfin
    (siegel_density_unit_ball_integral_finite n hn D hm hd hfin)
    (siegel_density_residue_class_bound n hn)

theorem primitive_orbit_compact_finiteness (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet
    D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) :
    IsFiniteMeasureOnCompacts (primitiveOrbitMeasure D)  := by
  obtain ⟨b, hb, hle⟩ := siegel_density_ball_majorant n hn D hm hd hfin
  apply primitive_orbit_compact_of_finite_density_work D
  intro j
  exact ne_top_of_le_ne_top hb (lintegral_mono_ae (hle j))

theorem coordinate_patch_translation_gluing {n : ℕ} (μ : Measure (E n)) (i : Fin n) (t : ℝ)
    (h : ∀ j : Fin n, j ≠ i →
      (μ.map (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·)).restrict {x | x j ≠ 0} =
        μ.restrict {x | x j ≠ 0}) :
    (μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ).map
      (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·) =
      μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ :=
  axisComplementTranslation_of_patches μ i t h

theorem sl_invariant_translate_off_coordinate_axis (n : ℕ) (hn : 2 ≤ n) (μ : Measure (E n)) (hz : μ
    {0} = 0) (hf : IsFiniteMeasureOnCompacts μ) (hi : ∀ g : SL n, Measure.map (fun x : E n ↦
    WithLp.toLp 2 (g • WithLp.ofLp x)) (μ) = μ) : ∀ (i : Fin n) (t : ℝ), 
    let ν := μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ; ν.map (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·) = ν := by
  intro i t
  exact coordinate_patch_translation_gluing μ i t (sl_invariant_translate_on_coordinate_patch n hn μ hz hf hi i t)

private theorem scalarVolume_of_axisComplementTranslations {n : ℕ} (μ : Measure (E n))
    [IsFiniteMeasureOnCompacts μ]
    (hnull : ∀ i : Fin n, μ {x | ∀ j ≠ i, x j = 0} = 0)
    (htrans : ∀ (i : Fin n) (t : ℝ),
      let ν := μ.restrict {x : E n | ∀ j ≠ i, x j = 0}ᶜ
      ν.map (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·) = ν) :
    ∃ C : ℝ≥0∞, μ = C • volume := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have coord (i : Fin n) (t : ℝ) : μ.map (t • b i + ·) = μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simpa using hnull i) : ∀ᵐ x ∂μ, x ∈ {y : E n | ∀ j ≠ i, y j = 0}ᶜ), b] using htrans i t
  have : μ.IsAddLeftInvariant := by
    constructor
    intro x
    let v := fun i ↦ b.repr x i • b i
    have sums (s : Finset (Fin n)) : μ.map ((∑ i ∈ s, v i) + ·) = μ := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
        rw [Finset.sum_insert his]
        have h := Measure.map_map (measurable_const_add (v i))
          (measurable_const_add (∑ j ∈ s, v j)) (μ := μ)
        simpa only [ih, coord, Function.comp_def, ← add_assoc, v] using h.symm
    simpa only [v, b.sum_repr] using sums Finset.univ
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul μ volume⟩

theorem sl_invariant_measure_scalar_off_origin (n : ℕ) (hn : 2 ≤ n) (μ : Measure (E n)) (hz : μ {0}
    = 0) (hf : IsFiniteMeasureOnCompacts μ) (hi : ∀ g : SL n, Measure.map (fun x : E n ↦ WithLp.toLp
    2 (g • WithLp.ofLp x)) (μ) = μ) : ∃ C : ℝ≥0∞, μ = C • volume := by
  exact scalarVolume_of_axisComplementTranslations μ (sl_invariant_coordinate_axis_null n hn μ hz hf hi) (sl_invariant_translate_off_coordinate_axis n hn μ hz hf hi)

theorem primitive_orbit_origin_null {n : ℕ} (D : Set (SL n)) : primitiveOrbitMeasure D {0} = 0 :=
  primitiveOrbitMeasure_origin D

theorem primitive_orbit_measure_scalar (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) : ∃ C
    : ℝ≥0∞, primitiveOrbitMeasure D = C • volume := by
  exact sl_invariant_measure_scalar_off_origin n hn _ (primitive_orbit_origin_null D) (primitive_orbit_compact_finiteness n hn D hm hd hfin) (primitive_orbit_sl_invariance n hn D hm hd hfin)

theorem siegel_density_ball_unit (n j : ℕ) : ∫⁻ x, densityTest n j x = 1 := densityTest_unit n j

theorem siegel_unit_test_density_limit (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) : ∃ f
    : ℕ → E n → ℝ≥0∞, (∀ j, Measurable (f j)) ∧ (∀ j, ∫⁻ x, f j x = 1) ∧ Tendsto (fun j ↦ ∫⁻ g in D,
    tupleWorkload (fun v : Fin 1 → E n ↦ f j (v 0)) (QuotientGroup.mk g) ∂groupHaar n) atTop (𝓝
    (groupHaar n D)) := by
  exact ⟨densityTest n, densityTest_measurable n, siegel_density_ball_unit n, densityTest_limit_of_bound n D (siegel_density_ball_pointwise n hn) (siegel_density_ball_majorant n hn D hm hd hfin)⟩

theorem primitive_orbit_calibration_bridge {n : ℕ} {D : Set (SL n)} {C : ℝ≥0∞}
    (hC : primitiveOrbitMeasure D = C • volume)
    (f : ℕ → E n → ℝ≥0∞) (hf : ∀ j, Measurable (f j))
    (unit : ∀ j, ∫⁻ x, f j x = 1)
    (limit : Tendsto (fun j ↦ ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f j (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) atTop (𝓝 (groupHaar n D))) :
    (∀ u : E n → ℝ≥0∞, Measurable u →
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val = C * ∫⁻ x, u x) ∧
      C * ∑' k, dilationWeight n k = groupHaar n D := primitiveOrbit_calibration hC f hf unit limit

theorem siegel_primitive_orbit_covolume (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) :
    ∃ C : ℝ≥0∞, (∀ (u : E n → ℝ≥0∞), Measurable u →
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val = C * ∫⁻ x, u x) ∧
      C * ∑' k, dilationWeight n k = groupHaar n D := by
  obtain ⟨C, hC⟩ := primitive_orbit_measure_scalar n hn D hm hd hfin
  obtain ⟨f, hf, hu, hl⟩ := siegel_unit_test_density_limit n hn D hm hd hfin
  exact ⟨C, primitive_orbit_calibration_bridge hC f hf hu hl⟩

theorem siegel_domain_unfolding_evaluation (n : ℕ) (hn : 2 ≤ n) (D : Set (SL n)) (hm : MeasurableSet
    D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) (f
    : E n → ℝ≥0∞) (hf : Measurable f) : (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
    (QuotientGroup.mk g) ∂groupHaar n) = groupHaar n D * ∫⁻ x, f x := by
  obtain ⟨C, prim, mass⟩ := siegel_primitive_orbit_covolume n hn D hm hd hfin
  exact siegel_positive_dilations_of_primitive_vectors D C prim mass f hf

end SigabaNeo.Rogers
