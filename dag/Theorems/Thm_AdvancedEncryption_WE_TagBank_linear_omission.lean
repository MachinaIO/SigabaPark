import Mathlib
/-- Arbitrary public linear combinations of issued monomials have zero missing coefficient. -/
theorem AdvancedEncryption.WE.TagBank.linear_omission {R : Type*} [Semiring R] (S : Finset ℕ) (M : ℕ) (hm : M ∉ S) (c : ℕ → R) :
    (∑ d ∈ S, Polynomial.monomial d (c d)).coeff M = 0 := by sorry
