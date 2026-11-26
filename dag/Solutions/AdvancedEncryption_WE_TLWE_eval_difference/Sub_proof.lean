import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Abel

open Matrix SigabaNeo.Lattices

theorem solution {R : Type*} [CommRing R] {r W ι : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (A : ι → Matrix r W R) (x : ι → R)
    (s₁ s₂ : Matrix (Fin 1) r R) (c₁ c₂ e₁ e₂ : ι → Matrix (Fin 1) W R)
    (h₁ : ∀ i, c₁ i = s₁ * (A i - x i • Γ.G) + e₁ i)
    (h₂ : ∀ i, c₂ i = s₂ * (A i - x i • Γ.G) + e₂ i) (f : Circuit ι) :
    evalEnc Γ A x c₁ f - evalEnc Γ A x c₂ f =
      (s₁ - s₂) * (evalMat Γ A f - f.eval x • Γ.G) + evalErr Γ A x (fun i => e₁ i - e₂ i) f := by
  have hd : ∀ i, (fun i => c₁ i - c₂ i) i = (s₁ - s₂) * (A i - x i • Γ.G) + (fun i => e₁ i - e₂ i) i := by
    intro i; simp only [h₁, h₂, Matrix.sub_mul]; abel
  have hlin : ∀ g : Circuit ι, evalErr Γ A x c₁ g - evalErr Γ A x c₂ g =
      evalErr Γ A x (fun i => c₁ i - c₂ i) g := by
    intro g
    induction g with
    | input i => rfl
    | one => simp [evalErr]
    | nand a b iha ihb =>
      simp only [evalErr, ← iha, ← ihb, Matrix.sub_mul, smul_sub]
      abel
  have := bgg_key_relation Γ (s₁ - s₂) A x (fun i => c₁ i - c₂ i) (fun i => e₁ i - e₂ i) hd f
  simp only [evalEnc] at this ⊢
  rw [hlin f, this]
