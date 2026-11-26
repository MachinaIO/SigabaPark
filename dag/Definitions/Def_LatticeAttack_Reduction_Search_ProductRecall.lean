module

public import Mathlib.Probability.Independence.Basic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Search

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- For a fixed regular rotation, a global miss forces one block to miss on every draw.
Independence is required only within each block. -/
theorem productCodeMiss_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {m B : ℕ} (fail : Fin m → Fin B → Set Ω) (miss : Set Ω) (q : ℝ≥0∞)
    (hm : ∀ i j, MeasurableSet (fail i j)) (hi : ∀ i, iIndepSet (fail i) μ)
    (hq : ∀ i j, μ (fail i j) ≤ q)
    (cover : miss ⊆ ⋃ i, ⋂ j, fail i j) : μ miss ≤ m • q ^ B := by
  classical
  calc
    μ miss ≤ μ (⋃ i, ⋂ j, fail i j) := measure_mono cover
    _ ≤ ∑ i, μ (⋂ j, fail i j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin m, q ^ B := by
      apply Finset.sum_le_sum
      intro i _
      have h := (iIndepSet_iff_meas_biInter (hm i)).mp (hi i) Finset.univ
      simp only [Finset.mem_univ, Set.iInter_true] at h
      rw [h]
      simpa using Finset.prod_le_prod (s := Finset.univ) (fun j _ ↦ hq i j)
    _ = _ := by simp

#print axioms productCodeMiss_le

end SigabaNeo.Lattices.Search
