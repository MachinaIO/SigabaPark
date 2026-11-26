import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRHaarUniqueness

set_option autoImplicit true

open MeasureTheory

namespace SigabaNeo.Rogers

private theorem map_sum_translation {d : ℕ} (μ : Measure (ColumnParameters d))
    {ι : Type*} (v : ι → ColumnParameters d) (s : Finset ι)
    (h : ∀ i, μ.map (v i + ·) = μ) : μ.map ((∑ i ∈ s, v i) + ·) = μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have e := congrArg (Measure.map (v i + ·)) ih
    rw [Measure.map_map (measurable_const_add _) (measurable_const_add _), h] at e
    simpa [Function.comp_def, add_assoc] using e

theorem rootBlock_of_axes {d : ℕ} (μ : Measure (ColumnParameters d))
    (h : ∀ i : Fin d, ∀ r : ℝ, μ.map (((Pi.single i r, 0) : ColumnParameters d) + ·) = μ)
    (t : Fin d → ℝ) : μ.map (((t, 0) : ColumnParameters d) + ·) = μ := by
  classical
  have e := map_sum_translation μ (fun i ↦ ((Pi.single i (t i), 0) : ColumnParameters d))
    Finset.univ (fun i ↦ h i (t i))
  have eq : (∑ i, ((Pi.single i (t i), 0) : ColumnParameters d)) = (t, 0) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]
  rwa [eq] at e

theorem upperBlock_of_axes {d : ℕ} (μ : Measure (ColumnParameters d))
    (h : ∀ i : UpperEntry (d+1), ∀ r : ℝ,
      μ.map (((0, Pi.single i r) : ColumnParameters d) + ·) = μ)
    (u : UpperEntry (d+1) → ℝ) : μ.map (((0, u) : ColumnParameters d) + ·) = μ := by
  classical
  have e := map_sum_translation μ (fun i ↦ ((0, Pi.single i (u i)) : ColumnParameters d))
    Finset.univ (fun i ↦ h i (u i))
  have eq : (∑ i, ((0, Pi.single i (u i)) : ColumnParameters d)) = (0, u) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]
  rwa [eq] at e

#print axioms rootBlock_of_axes
#print axioms upperBlock_of_axes
end SigabaNeo.Rogers
