import Mathlib.Data.Matrix.Mul

open Matrix

theorem AdvancedEncryption.WE.IPE.weighted_attribute_factorization {R I J K : Type*} [CommRing R] [Fintype I] [Fintype J] [Fintype K]
    (A : Matrix I J R) (T : Matrix J K R)
    (x y : I → R) (x' : J → R) (y' : K → R)
    (hx : x = A *ᵥ x') (hy : y ᵥ* A = T *ᵥ y') :
    y ⬝ᵥ x = (x' ᵥ* T) ⬝ᵥ y' := by
  sorry
