import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

theorem solution {K : Type*} [CommRing K] {n k : ℕ}
    (A G : Matrix (Fin n) (Fin k) K) (s s' : Fin n → K) (P : K) (e ec : Fin k → K)
    (Kh c : Fin k → K)
    (hK : Kh = s ᵥ* A + e - s' ᵥ* G) (hc : c = s ᵥ* (A - P • G) + ec) :
    Kh - c = (P • s - s') ᵥ* G + (e - ec) := by
  subst hK hc
  simp only [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.sub_vecMul, Matrix.smul_vecMul]
  abel
