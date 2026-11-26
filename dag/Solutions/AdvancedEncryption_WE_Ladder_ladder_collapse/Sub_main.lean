import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

theorem solution {K : Type*} [CommRing K] {n m k : ℕ}
    (G : Matrix (Fin n) (Fin k) K)
    (Ginv : Matrix (Fin n) (Fin m) K → Matrix (Fin k) (Fin m) K)
    (hG : ∀ X, G * Ginv X = X)
    (s : ℕ → Fin n → K) (B : ℕ → Matrix (Fin n) (Fin k) K) (e : ℕ → Fin k → K)
    (Kh : ℕ → Fin k → K)
    (hK : ∀ i, Kh i = s (i + 1) ᵥ* B (i + 1) + e i - s i ᵥ* G)
    (M : ℕ → Matrix (Fin n) (Fin m) K) (y ε r : ℕ → Fin m → K)
    (hM : ∀ i, M (i + 1) = B (i + 1) * Ginv (M i))
    (hy : ∀ i, y (i + 1) = y i + Kh i ᵥ* Ginv (M i) + r i)
    (hε : ∀ i, ε (i + 1) = ε i + e i ᵥ* Ginv (M i) + r i)
    (h0 : y 0 = s 0 ᵥ* M 0 + ε 0) :
    ∀ i, y i = s i ᵥ* M i + ε i := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih =>
    have key : s i ᵥ* G ᵥ* Ginv (M i) = s i ᵥ* M i := by
      rw [Matrix.vecMul_vecMul, hG]
    rw [hy, hε, hM, hK, ih, Matrix.sub_vecMul, Matrix.add_vecMul, key,
      ← Matrix.vecMul_vecMul]
    abel
