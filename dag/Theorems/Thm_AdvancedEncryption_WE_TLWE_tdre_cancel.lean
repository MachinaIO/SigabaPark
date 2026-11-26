import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices

theorem AdvancedEncryption.WE.TLWE.tdre_cancel {R : Type*} [CommRing R] {n m : Type*} [Fintype n]
    (A : Matrix n m R) (s₁ s₂ : Matrix (Fin 1) n R) (e₁ e₂ : Matrix (Fin 1) m R) :
    (s₁ * A + e₁) - (s₂ * A + e₂) = (s₁ - s₂) * A + (e₁ - e₂) := by sorry
