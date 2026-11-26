import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ι μ : Type*} [CommRing R] [Fintype ι] [Fintype μ] [DecidableEq ι]
    (A : Matrix ι μ R) (K : Matrix μ ι R) (hK : A * K = 1) :
    (∀ s s' : ι → R, s ᵥ* A = s' ᵥ* A → s = s') ∧
      ∀ (s : ι → R) (e : μ → R), (s ᵥ* A + e) ᵥ* K = s + e ᵥ* K := by
  refine ⟨fun s s' h => ?_, fun s e => ?_⟩
  · have := congrArg (fun v => v ᵥ* K) h
    simpa [Matrix.vecMul_vecMul, hK] using this
  · rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, hK, Matrix.vecMul_one]
