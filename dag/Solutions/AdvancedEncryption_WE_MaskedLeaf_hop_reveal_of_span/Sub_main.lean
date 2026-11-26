import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k n : ℕ}
    (c : ι → Fin k → R) (t : ι) (β : ι → R)
    (hrel : c t = ∑ z, β z • c z) (M : ι → Fin n → R) (e : ι → Fin n → R)
    (A : Matrix (Fin k) (Fin n) R) :
    (M t + c t ᵥ* A + e t) - ∑ z, β z • (M z + c z ᵥ* A + e z) =
      (M t - ∑ z, β z • M z) + (e t - ∑ z, β z • e z) := by
  have h1 : ∑ z, β z • (c z ᵥ* A) = c t ᵥ* A := by
    rw [hrel, Matrix.sum_vecMul]; simp [Matrix.smul_vecMul]
  simp only [smul_add, Finset.sum_add_distrib, h1]
  abel
