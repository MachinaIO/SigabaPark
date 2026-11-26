import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring

/-- **Tensor products of noisy samples (note `pq-we-native-hop-designs`, §3, direction (b)).**
`(Y₁ + E₁) ⊗ (Y₂ + E₂) = Y₁ ⊗ Y₂ + (E₁ ⊗ Y₂ + Y₁ ⊗ E₂ + E₁ ⊗ E₂)`. With `Y_i = s_iᵀA_i` uniform
mod `q` and `E_i` small, the cross terms `E₁ ⊗ Y₂` and `Y₁ ⊗ E₂` are not small, so tensor-LWE
samples with witness-selected factors cannot be combined by plain tensoring; one factor must be
short (a preimage or a `G^{-1}`), which leads back to GGH15 or GSW chains. -/
theorem AdvancedEncryption.WE.NativeHop.kron_noise_cross {R : Type*} [CommRing R] {l m n p : Type*}
    (Y₁ E₁ : Matrix l m R) (Y₂ E₂ : Matrix n p R) :
    Matrix.kroneckerMap (· * ·) (Y₁ + E₁) (Y₂ + E₂) =
      Matrix.kroneckerMap (· * ·) Y₁ Y₂ +
        (Matrix.kroneckerMap (· * ·) E₁ Y₂ + Matrix.kroneckerMap (· * ·) Y₁ E₂ +
          Matrix.kroneckerMap (· * ·) E₁ E₂) := by sorry
