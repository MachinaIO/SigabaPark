import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

theorem solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] {ι κ : Type*} [Fintype ι] (v : κ → ι → V)
    (hv : ∀ k, LinearIndependent K (v k)) (L : κ → V →ₗ[K] W)
    (hL : ∀ k, Function.Injective (L k)) (bad : κ → ι → Prop) [∀ k i, Decidable (bad k i)]
    (α : ι → K) (h : ∀ k, L k (∑ i, (if bad k i then α i else 0) • v k i) = 0) :
    ∀ k i, bad k i → α i = 0 := by
  intro k i hki
  have hs : ∑ i, (if bad k i then α i else 0) • v k i = 0 :=
    (injective_iff_map_eq_zero (L k)).1 (hL k) _ (h k)
  have := Fintype.linearIndependent_iff.1 (hv k) _ hs i
  simpa [hki] using this
