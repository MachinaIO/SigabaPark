import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

theorem solution {K : Type*} [CommRing K] {n m k k' : ℕ}
    (A : Matrix (Fin n) (Fin k) K) (B : Matrix (Fin n) (Fin k') K)
    (G : Matrix (Fin n) (Fin k) K) (G' : Matrix (Fin n) (Fin k') K)
    (Mp : Matrix (Fin n) (Fin m) K) (X : Matrix (Fin k) (Fin m) K) (X' : Matrix (Fin k') (Fin m) K)
    (hGX : G * X = Mp) (hGX' : G' * X' = Mp) (hBX : B * X' = A * X)
    (s s' : Fin n → K) (P : K) (e : Fin k' → K) (ec : Fin k → K) (ε : Fin m → K)
    (Kh : Fin k' → K) (c : Fin k → K) (y : Fin m → K)
    (hK : Kh = s ᵥ* B + e - s' ᵥ* G') (hc : c = s ᵥ* (A - P • G) + ec)
    (hy : y = s' ᵥ* Mp + ε) :
    y + Kh ᵥ* X' - c ᵥ* X = P • (s ᵥ* Mp) + (ε + e ᵥ* X' - ec ᵥ* X) := by
  subst hK hc hy
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_sub,
    Matrix.vecMul_smul, hGX', hBX]
  rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, hGX]
  abel
