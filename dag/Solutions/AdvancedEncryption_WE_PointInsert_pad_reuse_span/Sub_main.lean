import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ι μ ν : Type*} [CommRing R] [Fintype μ] (c : ι → μ → R)
    (U : Matrix μ ν R) (π : ι) (s : Finset ι) (lam : ι → R)
    (h : c π = ∑ x ∈ s, lam x • c x) :
    c π ᵥ* U = ∑ x ∈ s, lam x • (c x ᵥ* U) := by
  classical
  have key : ∀ t : Finset ι, (∑ x ∈ t, lam x • c x) ᵥ* U = ∑ x ∈ t, lam x • (c x ᵥ* U) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_vecMul, ih, Matrix.smul_vecMul]
  rw [h, key]
