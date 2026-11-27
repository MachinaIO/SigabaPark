import Mathlib
/-- Arbitrary public linear combinations of issued monomials have zero missing coefficient. -/
theorem solution {R : Type*} [Semiring R] (S : Finset ℕ) (M : ℕ) (hm : M ∉ S) (c : ℕ → R) :
    (∑ d ∈ S, Polynomial.monomial d (c d)).coeff M = 0 := by
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro d hd
  exact Polynomial.coeff_monomial_of_ne _ (fun h => hm (h ▸ hd))
