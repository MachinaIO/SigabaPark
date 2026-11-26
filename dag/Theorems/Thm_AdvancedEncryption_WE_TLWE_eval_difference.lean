import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices

theorem AdvancedEncryption.WE.TLWE.eval_difference {R : Type*} [CommRing R] {r W ι : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (A : ι → Matrix r W R) (x : ι → R)
    (s₁ s₂ : Matrix (Fin 1) r R) (c₁ c₂ e₁ e₂ : ι → Matrix (Fin 1) W R)
    (h₁ : ∀ i, c₁ i = s₁ * (A i - x i • Γ.G) + e₁ i)
    (h₂ : ∀ i, c₂ i = s₂ * (A i - x i • Γ.G) + e₂ i) (f : Circuit ι) :
    evalEnc Γ A x c₁ f - evalEnc Γ A x c₂ f =
      (s₁ - s₂) * (evalMat Γ A f - f.eval x • Γ.G) + evalErr Γ A x (fun i => e₁ i - e₂ i) f := by sorry
