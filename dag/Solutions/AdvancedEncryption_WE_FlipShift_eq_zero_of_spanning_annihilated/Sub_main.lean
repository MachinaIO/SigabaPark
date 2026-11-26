import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {K X κ μ : Type*} [Field K] [Fintype κ] [Fintype μ] [DecidableEq κ]
    (c : X → κ → K) (hspan : Submodule.span K (Set.range c) = ⊤)
    (M : Matrix κ μ K) (h : ∀ x, c x ᵥ* M = 0) : M = 0 := by
  have hall : ∀ v ∈ Submodule.span K (Set.range c), v ᵥ* M = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨x, rfl⟩ := hv; exact h x
    | zero => simp
    | add u v _ _ hu hv => rw [Matrix.add_vecMul, hu, hv, add_zero]
    | smul a v _ hv => rw [Matrix.smul_vecMul, hv, smul_zero]
  ext i j
  have := congrFun (hall (Pi.single i 1) (by rw [hspan]; trivial)) j
  simpa [Matrix.single_one_vecMul] using this
