import Mathlib
open Finset

theorem AdvancedEncryption.WE.LiftedProduct.orthogonality {R : Type*} [CommRing R] (d : ℕ) (z : R) (hz : z^(2^d) = -1)
    (k : ℕ) (hk : 0 < k) (hmax : k < 2^(d+1)) :
    ∑ i ∈ range (2^(d+1)), (z^k)^i = 0 := by sorry
