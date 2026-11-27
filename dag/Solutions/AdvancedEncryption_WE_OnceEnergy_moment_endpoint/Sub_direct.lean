import Mathlib.LinearAlgebra.Lagrange
open Polynomial Finset
open scoped Polynomial
/-- A single family of public weights transports all bounded-degree energy readouts to zero. -/
theorem solution {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (hs : s.Nonempty) :
    ∃ weights : K → K, (∑ i ∈ s, weights i) = 1 ∧
      ∀ f : K[X], f.degree < s.card → (∑ i ∈ s, f.eval i * weights i) = f.eval 0 := by
  let weights := fun i => (Lagrange.basis s id i).eval 0
  refine ⟨weights,?_,?_⟩
  · have h := congrArg (fun f : K[X] => f.eval 0) (Lagrange.sum_basis (v := id) Function.injective_id.injOn hs)
    simpa [weights,eval_finsetSum] using h
  · intro f hf
    have h := congrArg (fun g : K[X] => g.eval 0) (Lagrange.eq_interpolate (v := id) Function.injective_id.injOn hf)
    simpa [weights,Lagrange.interpolate_apply,eval_finsetSum] using h.symm
