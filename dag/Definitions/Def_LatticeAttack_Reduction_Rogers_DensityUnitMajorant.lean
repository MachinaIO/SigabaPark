import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests

set_option autoImplicit true

open MeasureTheory
open scoped ENNReal NNReal

namespace SigabaNeo.Rogers

/-- A uniform comparison with the unit-ball count reduces domination to a single integral. -/
theorem densityMajorant_of_unitComparison (n : ℕ) (D : Set (SL n))
    (hfin : groupHaar n D ≠ ⊤)
    (unitMass : (∫⁻ g in D, densityWork n 0 g ∂groupHaar n) ≠ ⊤)
    (comparison : ∃ C : ℝ≥0, ∀ j g, densityWork n j g ≤ (C : ℝ≥0∞) * (1 + densityWork n 0 g)) :
    ∃ b : SL n → ℝ≥0∞, (∫⁻ g in D, b g ∂groupHaar n) ≠ ⊤ ∧
      ∀ j, densityWork n j ≤ᵐ[(groupHaar n).restrict D] b := by
  obtain ⟨C, hC⟩ := comparison
  refine ⟨fun g ↦ C * (1 + densityWork n 0 g), ?_, fun j ↦ Filter.Eventually.of_forall (hC j)⟩
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left measurable_const]
  apply ENNReal.mul_ne_top ENNReal.coe_ne_top
  simpa [lintegral_const, hfin] using
    (ENNReal.add_ne_top.mpr ⟨hfin, unitMass⟩)

#print axioms densityMajorant_of_unitComparison

end SigabaNeo.Rogers
