import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices

theorem AdvancedEncryption.WE.TLWE.linear_closure {R : Type*} [CommRing R] {k n m p : Type*} [Fintype k] [Fintype n] [Fintype m]
    (M : Matrix k m R) (A : Matrix n p R) (t : Matrix (Fin 1) k R) (E ct : Matrix (Fin 1) m R)
    (hct : ct = t * M + E) (L₁ L₂ : Matrix m p R) (Q₁ Q₂ : Matrix k n R)
    (h₁ : M * L₁ = Q₁ * A) (h₂ : M * L₂ = Q₂ * A) (a b : R) :
    ct * (a • L₁ + b • L₂) = (t * (a • Q₁ + b • Q₂)) * A + E * (a • L₁ + b • L₂) := by sorry
