import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRHaarUniqueness

set_option autoImplicit true

open MeasureTheory Set
open scoped ENNReal

namespace SigabaNeo.Rogers

theorem flatInvariant_of_coordinate_blocks {d : ℕ} (μ : Measure (ColumnParameters d))
    (hr : ∀ t : Fin d → ℝ, μ.map (((t, 0) : ColumnParameters d) + ·) = μ)
    (hu : ∀ u : UpperEntry (d+1) → ℝ, μ.map (((0, u) : ColumnParameters d) + ·) = μ) :
    μ.IsAddLeftInvariant := by
  constructor
  rintro ⟨t, u⟩
  have h := congrArg (Measure.map (((t, 0) : ColumnParameters d) + ·)) (hu u)
  rw [Measure.map_map (measurable_const_add _) (measurable_const_add _), hr] at h
  simpa [Function.comp_def, ← add_assoc] using h

theorem flatFinite_of_compact_preimage {d : ℕ} (f : SL (d+1) → ColumnParameters d)
    (hf : Measurable f)
    (hpre : ∀ K : Set (ColumnParameters d), IsCompact K → IsCompact (f ⁻¹' K)) :
    IsFiniteMeasureOnCompacts (flatColumnMeasure ((groupHaar (d+1)).map f)) := by
  constructor
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hn
  · simp
  let w (p : ColumnParameters d) := (columnRootWeight d p.1)⁻¹
  have hpos (p : ColumnParameters d) : columnRootWeight d p.1 ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact Finset.prod_pos fun i _ ↦ Real.exp_pos _
  have hc : Continuous w := by
    unfold w columnRootWeight
    apply Continuous.fun_inv
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  obtain ⟨q, _, hq⟩ := hK.exists_isMaxOn hn hc.continuousOn
  rw [flatColumnMeasure, withDensity_apply _ hK.measurableSet]
  change (∫⁻ p in K, w p ∂_) < ⊤
  apply lt_of_le_of_lt (setLIntegral_mono' hK.measurableSet (fun p hp ↦ hq hp))
  rw [setLIntegral_const, Measure.map_apply hf hK.measurableSet]
  let : IsFiniteMeasureOnCompacts (groupHaar (d+1)) := by unfold groupHaar; infer_instance
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (hpos q)))
    (hpre K hK).measure_lt_top

end SigabaNeo.Rogers
