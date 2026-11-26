import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

/-- GSW multiplication in row-vector form: products of GSW ciphertexts stay of the form value times t^T G plus noise, so homomorphic evaluation of a PRF under GSW ends in the same rounding object. Used in the note `pq-we-ladder-and-homomorphic-prf`. -/
theorem AdvancedEncryption.WE.Ladder.gsw_mul {K : Type*} [CommRing K] {n k : ℕ}
    (G : Matrix (Fin n) (Fin k) K)
    (X2 : Matrix (Fin k) (Fin k) K)
    (t : Fin n → K) (C1 C2 : Matrix (Fin n) (Fin k) K) (x1 x2 : K) (e1 e2 : Fin k → K)
    (hX : G * X2 = C2)
    (h1 : t ᵥ* C1 = x1 • (t ᵥ* G) + e1) (h2 : t ᵥ* C2 = x2 • (t ᵥ* G) + e2) :
    t ᵥ* (C1 * X2) = (x1 * x2) • (t ᵥ* G) + (x1 • e2 + e1 ᵥ* X2) := by sorry
