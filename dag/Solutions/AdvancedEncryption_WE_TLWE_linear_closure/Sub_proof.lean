import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Module

open Matrix SigabaNeo.Lattices

theorem solution {R : Type*} [CommRing R] {k n m p : Type*} [Fintype k] [Fintype n] [Fintype m]
    (M : Matrix k m R) (A : Matrix n p R) (t : Matrix (Fin 1) k R) (E ct : Matrix (Fin 1) m R)
    (hct : ct = t * M + E) (L₁ L₂ : Matrix m p R) (Q₁ Q₂ : Matrix k n R)
    (h₁ : M * L₁ = Q₁ * A) (h₂ : M * L₂ = Q₂ * A) (a b : R) :
    ct * (a • L₁ + b • L₂) = (t * (a • Q₁ + b • Q₂)) * A + E * (a • L₁ + b • L₂) := by
  subst hct
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    h₁, h₂]
  module
