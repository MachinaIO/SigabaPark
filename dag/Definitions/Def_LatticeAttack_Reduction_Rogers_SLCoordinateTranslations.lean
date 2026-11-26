module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

/-- Translation invariance away from each null coordinate axis suffices for Haar uniqueness. -/
theorem scalarVolume_of_axisComplementTranslations {n : ℕ} (μ : Measure (E n))
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

end SigabaNeo.Rogers
