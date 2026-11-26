import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k : ℕ}
    (c : ι → Fin k → K) (z₀ : ι)
    (hspan : Submodule.span K (Set.range fun z => c z - c z₀) = ⊤) :
    ∃ α : ι → K, ∑ z, α z = 1 ∧ ∑ z, α z • c z = 0 := by
  classical
  have hm : -c z₀ ∈ Submodule.span K (Set.range fun z => c z - c z₀) := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨β, hβ⟩ := hm
  refine ⟨fun z => β z + if z = z₀ then 1 - ∑ y, β y else 0, ?_, ?_⟩
  · simp [Finset.sum_add_distrib]
  · simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    have : ∑ z, β z • (c z - c z₀) = ∑ z, β z • c z - (∑ z, β z) • c z₀ := by
      simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [this] at hβ
    rw [sub_smul, one_smul]
    have h2 : ∑ z, β z • c z = (∑ z, β z) • c z₀ - c z₀ := by
      rw [sub_eq_neg_add, ← hβ]; abel
    rw [h2]; abel
