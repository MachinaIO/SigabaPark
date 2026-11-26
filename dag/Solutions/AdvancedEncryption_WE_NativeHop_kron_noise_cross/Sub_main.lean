import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring

theorem solution {R : Type*} [CommRing R] {l m n p : Type*}
    (Y₁ E₁ : Matrix l m R) (Y₂ E₂ : Matrix n p R) :
    Matrix.kroneckerMap (· * ·) (Y₁ + E₁) (Y₂ + E₂) =
      Matrix.kroneckerMap (· * ·) Y₁ Y₂ +
        (Matrix.kroneckerMap (· * ·) E₁ Y₂ + Matrix.kroneckerMap (· * ·) Y₁ E₂ +
          Matrix.kroneckerMap (· * ·) E₁ E₂) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [Matrix.kroneckerMap_apply]
  ring
