import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit true

/-! Real-valued section integration for finite measurable product sets. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open MeasureTheory

/-- Taking real values in Tonelli is valid because finite total measure makes
almost every section finite. -/
theorem integral_section_volume {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure β)] {S : Set (α × β)}
    (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    (∫ x, volume.real (Prod.mk x ⁻¹' S)) = volume.real S := by
  have hm := (measurable_measure_prodMk_left (ν := (volume : Measure β)) hS).aemeasurable (μ := (volume : Measure α))
  have hf := Measure.ae_measure_lt_top (μ := (volume : Measure α)) hS hfin
  simpa only [Measure.real, Measure.volume_eq_prod, ← Measure.prod_apply hS] using integral_toReal hm hf

#print axioms integral_section_volume
end SigabaNeo.Wall1.RawBallRounding
