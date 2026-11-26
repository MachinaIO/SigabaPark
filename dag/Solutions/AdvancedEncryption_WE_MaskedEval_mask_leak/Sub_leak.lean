import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Matrix SigabaNeo.Lattices

theorem solution {R : Type*} [CommRing R]
    {r W ι Z X : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (s : Matrix (Fin 1) r R) (A : ι → Matrix r W R) (x : ι → R)
    (c e : ι → Matrix (Fin 1) W R) (hc : ∀ i, c i = s * (A i - x i • Γ.G) + e i)
    (f : Z → Circuit ι) (stmt : Z → X) (P : X → Matrix (Fin 1) W R)
    (O η : Z → Matrix (Fin 1) W R)
    (hO : ∀ z, O z = s * evalMat Γ A (f z) + P (stmt z) + η z)
    (z₀ z₁ zs : Z) (hst : stmt z₀ = stmt z₁) (hv : (f z₁).eval x - (f z₀).eval x = 1) :
    (O zs - evalEnc Γ A x c (f zs)) - (f zs).eval x •
        ((O z₁ - evalEnc Γ A x c (f z₁)) - (O z₀ - evalEnc Γ A x c (f z₀))) =
      P (stmt zs) + (η zs - evalErr Γ A x e (f zs)) - (f zs).eval x •
        ((η z₁ - evalErr Γ A x e (f z₁)) - (η z₀ - evalErr Γ A x e (f z₀))) := by
  have key : ∀ z, O z - evalEnc Γ A x c (f z) =
      P (stmt z) + (f z).eval x • (s * Γ.G) + (η z - evalErr Γ A x e (f z)) := by
    intro z
    rw [hO z, bgg_key_relation Γ s A x c e hc (f z), Matrix.mul_sub, Matrix.mul_smul]
    abel
  rw [key zs, key z₁, key z₀, hst]
  have h1 : (f z₁).eval x = (f z₀).eval x + 1 := by rw [← hv]; ring
  rw [h1, add_smul, one_smul]
  module
