import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Abel

open Matrix SigabaNeo.Lattices

theorem solution {R : Type*} [CommRing R] {r W ι : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (Ω : ι → Matrix r W R) (x : ι → R) (ρ : Matrix (Fin 1) r R)
    (E ν : ι → Matrix (Fin 1) W R) (hE : ∀ i, E i = ρ * (Ω i - x i • Γ.G) + ν i)
    (f₁ f₂ : Circuit ι) (hv : f₁.eval x = f₂.eval x) :
    evalEnc Γ Ω x E f₁ - evalEnc Γ Ω x E f₂ =
      ρ * (evalMat Γ Ω f₁ - evalMat Γ Ω f₂) + (evalErr Γ Ω x ν f₁ - evalErr Γ Ω x ν f₂) := by
  rw [bgg_key_relation Γ ρ Ω x E ν hE f₁, bgg_key_relation Γ ρ Ω x E ν hE f₂, hv,
    Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub]
  abel
