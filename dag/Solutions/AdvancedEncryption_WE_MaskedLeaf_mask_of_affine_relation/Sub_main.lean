import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k n : ℕ}
    (c : ι → Fin k → R) (α : ι → R) (hα : ∑ z, α z = 1) (hrel : ∑ z, α z • c z = 0)
    (m : Fin n → R) (A : Matrix (Fin k) (Fin n) R) :
    ∑ z, α z • (m + c z ᵥ* A) = m := by
  have h1 : ∑ z, α z • (c z ᵥ* A) = (∑ z, α z • c z) ᵥ* A := by
    rw [Matrix.sum_vecMul]; simp [Matrix.smul_vecMul]
  simp only [smul_add, Finset.sum_add_distrib, h1, hrel, Matrix.zero_vecMul, add_zero,
    ← Finset.sum_smul, hα, one_smul]
