module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnHaarCoordinates

set_option autoImplicit true

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

def columnRootWeight (d : ℕ) (t : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i, Real.exp (-((i.val + 1 : ℕ) * ((d - i.val : ℕ) : ℝ)) * t i))

/-- Cancel the root density to compare the QR parameter law with additive Haar measure. -/
def flatColumnMeasure {d : ℕ} (μ : Measure (ColumnParameters d)) :=
  μ.withDensity (fun p ↦ (columnRootWeight d p.1)⁻¹)

theorem columnLaw_of_flat_invariance {d : ℕ} (μ : Measure (ColumnParameters d))
    [IsFiniteMeasureOnCompacts (flatColumnMeasure μ)]
    [(flatColumnMeasure μ).IsAddLeftInvariant] :
    ∃ C : ℝ, μ = ENNReal.ofReal C • (columnRootMeasure d).prod volume := by
  let w : ColumnParameters d → ℝ≥0∞ := fun p ↦ columnRootWeight d p.1
  have hm : Measurable (columnRootWeight d) := by unfold columnRootWeight; fun_prop
  have hw : Measurable w := hm.comp measurable_fst
  have hp (p : ColumnParameters d) : w p ≠ 0 := by
    dsimp [w, columnRootWeight]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Finset.prod_pos fun i _ ↦ Real.exp_pos _)
  have ht (p : ColumnParameters d) : w p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (flatColumnMeasure μ).withDensity w = μ := by
    unfold flatColumnMeasure
    change (μ.withDensity w⁻¹).withDensity w = μ
    rw [← withDensity_mul μ hw.inv hw]
    have h : w⁻¹ * w = 1 := funext fun p ↦ ENNReal.inv_mul_cancel (hp p) (ht p)
    rw [h, withDensity_one]
  let : (volume : Measure (ColumnParameters d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (μ := volume) (ν := volume)
  let c := Measure.addHaarScalarFactor (flatColumnMeasure μ) volume
  refine ⟨(c : ℝ), ?_⟩
  conv_lhs => rw [← hcancel]
  rw [Measure.isAddLeftInvariant_eq_smul (flatColumnMeasure μ) volume]
  change ((c : ℝ≥0∞) • volume).withDensity w = _
  rw [withDensity_smul_measure]
  change _ = ENNReal.ofReal (c : ℝ) • ((volume.withDensity (columnRootWeight d)).prod volume)
  rw [prod_withDensity_left hm, ENNReal.ofReal_coe_nnreal]
  rfl

#print axioms columnLaw_of_flat_invariance
end SigabaNeo.Rogers
