import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelSubgroup
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnChartCompact

set_option autoImplicit true

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace SigabaNeo.Rogers

private theorem rightInvariant_proportional {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (μ ν : Measure G) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsMulRightInvariant] [ν.IsMulRightInvariant] (hn : ν ≠ 0) :
    ∃ C : ℝ, μ = ENNReal.ofReal C • ν := by
  let s := spanningSets (μ.inv + ν.inv)
  have hex : ∃ i, ν.inv (s i) ≠ 0 := by
    by_contra! h
    have H := measure_iUnion_null h
    rw [show ⋃ i, s i = univ from iUnion_spanningSets _, measure_univ_eq_zero] at H
    apply hn
    rw [← ν.inv_inv, H]
    exact Measure.map_zero _
  obtain ⟨i,hi⟩ := hex
  have hfin := measure_spanningSets_lt_top (μ.inv + ν.inv) i
  change (μ.inv + ν.inv) (s i) < ⊤ at hfin
  rw [Measure.add_apply, ENNReal.add_lt_top] at hfin
  have hh := measure_eq_div_smul μ.inv ν.inv hi hfin.2.ne
  let c := μ.inv (s i) / ν.inv (s i)
  refine ⟨c.toReal, ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hfin.1.ne hi)]
  have e := congrArg Measure.inv hh
  rw [Measure.inv_inv] at e
  change μ = Measure.map Inv.inv (c • ν.inv) at e
  rw [Measure.map_smul _ measurable_inv.aemeasurable] at e
  exact e.trans (congrArg (c • ·) ν.inv_inv)

theorem columnLaw_of_borel_candidate {d : ℕ} (hd : 1 ≤ d) {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f)
    (h : (((columnRootMeasure d).prod volume).map columnBorelSection).IsMulRightInvariant) :
    ∃ C : ℝ, (groupHaar (d+1)).map f = ENNReal.ofReal C • (columnRootMeasure d).prod volume := by
  let : BorelSpace (SL (d+1)) := ⟨rfl⟩
  let e := (columnBorelMeasurableEquiv hf).symm
  let μ := (groupHaar (d+1)).map f
  let ν := (columnRootMeasure d).prod (volume : Measure (UpperEntry (d+1) → ℝ))
  let : IsFiniteMeasureOnCompacts μ := ⟨fun K hK ↦ by
    have : IsFiniteMeasureOnCompacts (groupHaar (d+1)) := by unfold groupHaar; infer_instance
    exact (Measure.map_apply hf.1 hK.measurableSet).symm ▸
      (columnChartCompactPreimage d hd f hf K hK).measure_lt_top⟩
  let : SigmaFinite (columnRootMeasure d) := by unfold columnRootMeasure; infer_instance
  let : SigmaFinite (μ.map e) := e.sigmaFinite_map
  let : SigmaFinite (ν.map e) := e.sigmaFinite_map
  let : (μ.map e).IsMulRightInvariant := by
    rw [show μ = _ from rfl, Measure.map_map e.measurable hf.1]
    exact columnBorel_chart_rightInvariant hf
  let : (ν.map e).IsMulRightInvariant := h
  have hn : columnRootMeasure d ≠ 0 := by
    intro H
    unfold columnRootMeasure at H
    obtain ⟨x,hx⟩ := ((withDensity_eq_zero_iff (Measurable.aemeasurable (by fun_prop))).mp H).exists
    exact (ENNReal.ofReal_ne_zero_iff.mpr (Finset.prod_pos fun i _ ↦ Real.exp_pos _)) hx
  have hν : ν ≠ 0 := by
    intro H
    have hval := congrArg (fun m : Measure (ColumnParameters d) ↦ m univ) H
    change ((columnRootMeasure d).prod volume) univ = 0 at hval
    rw [← univ_prod_univ, Measure.prod_prod] at hval
    exact (NeZero.ne volume) (by simpa [measure_univ_eq_zero, hn] using hval)
  let : SecondCountableTopology (Matrix (Fin (d+1)) (Fin (d+1)) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin (d+1) → Fin (d+1) → ℝ))
  let : SecondCountableTopology (SL (d+1)) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.secondCountableTopology
  let : SecondCountableTopology (columnBorel (d+1)) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (columnBorel (d+1)) := inferInstanceAs (BorelSpace {x : SL (d+1) // x ∈ columnBorel (d+1)})
  let : MeasurableMul₂ (columnBorel (d+1)) := ⟨continuous_mul.measurable⟩
  obtain ⟨C,hC⟩ := rightInvariant_proportional (μ.map e) (ν.map e)
    ((Measure.map_ne_zero_iff e.measurable.aemeasurable).mpr hν)
  exact ⟨C, by simpa only [e.map_symm_map, Measure.map_smul _ e.symm.measurable.aemeasurable]
    using congrArg (Measure.map e.symm) hC⟩

#print axioms columnLaw_of_borel_candidate
end SigabaNeo.Rogers
