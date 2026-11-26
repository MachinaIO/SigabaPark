import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {K V ι : Type*} [Field K] [Fintype V] [Fintype ι] [DecidableEq ι]
    (XA XB : V → ι → K) (T : Matrix ι ι K) (hT : IsUnit T.det)
    (h : ∀ x, XB x = XA x ᵥ* T) (c : V → K) :
    (∑ x, c x • XA x = 0) ↔ (∑ x, c x • XB x = 0) := by
  have key : ∑ x, c x • XB x = (∑ x, c x • XA x) ᵥ* T := by
    simp only [h, Matrix.sum_vecMul, Matrix.smul_vecMul]
  rw [key]
  constructor
  · intro h0; rw [h0, Matrix.zero_vecMul]
  · intro h0
    have := congrArg (fun v => v ᵥ* T⁻¹) h0
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hT] using this
