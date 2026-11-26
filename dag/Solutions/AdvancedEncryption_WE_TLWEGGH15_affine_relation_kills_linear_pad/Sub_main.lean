import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

theorem solution {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] {ι : Type*} [Fintype ι] (L : V →ₗ[R] W) (c : ι → V) (α : ι → R)
    (hα : ∑ z, α z = 1) (hrel : ∑ z, α z • c z = 0) (m : W) (e : ι → W) :
    ∑ z, α z • (m + L (c z) + e z) = m + ∑ z, α z • e z := by
  have h1 : ∑ z, α z • L (c z) = 0 := by
    simp_rw [← map_smul]; rw [← map_sum, hrel, map_zero]
  simp only [smul_add, Finset.sum_add_distrib, h1, add_zero, ← Finset.sum_smul, hα, one_smul]
