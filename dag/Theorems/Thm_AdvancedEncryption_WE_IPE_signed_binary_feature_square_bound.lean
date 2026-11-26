import Mathlib

open Finset
open scoped BigOperators

theorem AdvancedEncryption.WE.IPE.signed_binary_feature_square_bound {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ) (v : I → ℤ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) :
    (∑ j, (∑ i, v i * A i j)^2) ≤
      ∑ j, (max (∑ i, max (A i j) 0) (∑ i, max (-A i j) 0))^2 := by
  sorry
