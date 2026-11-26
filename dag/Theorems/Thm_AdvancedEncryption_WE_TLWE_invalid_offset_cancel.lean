import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices

theorem AdvancedEncryption.WE.TLWE.invalid_offset_cancel {R : Type*} [CommRing R] {r W ι : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (Ω : ι → Matrix r W R) (x : ι → R) (ρ : Matrix (Fin 1) r R)
    (E ν : ι → Matrix (Fin 1) W R) (hE : ∀ i, E i = ρ * (Ω i - x i • Γ.G) + ν i)
    (f₁ f₂ : Circuit ι) (hv : f₁.eval x = f₂.eval x) :
    evalEnc Γ Ω x E f₁ - evalEnc Γ Ω x E f₂ =
      ρ * (evalMat Γ Ω f₁ - evalMat Γ Ω f₂) + (evalErr Γ Ω x ν f₁ - evalErr Γ Ω x ν f₂) := by sorry
