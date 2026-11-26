import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

/-- Prefix exposure: if a last-level key-switching hint lies on a matrix B related to a BGG+ attribute matrix A by B X' = A X, with G X = G' X' = M_p (a prefix matrix), then hint, attribute encoding and the previous ladder value combine to a value-P sample of s on M_p. Used in the note `pq-we-ladder-and-homomorphic-prf`. -/
theorem AdvancedEncryption.WE.Ladder.prefix_exposure {K : Type*} [CommRing K] {n m k k' : ℕ}
    (A : Matrix (Fin n) (Fin k) K) (B : Matrix (Fin n) (Fin k') K)
    (G : Matrix (Fin n) (Fin k) K) (G' : Matrix (Fin n) (Fin k') K)
    (Mp : Matrix (Fin n) (Fin m) K) (X : Matrix (Fin k) (Fin m) K) (X' : Matrix (Fin k') (Fin m) K)
    (hGX : G * X = Mp) (hGX' : G' * X' = Mp) (hBX : B * X' = A * X)
    (s s' : Fin n → K) (P : K) (e : Fin k' → K) (ec : Fin k → K) (ε : Fin m → K)
    (Kh : Fin k' → K) (c : Fin k → K) (y : Fin m → K)
    (hK : Kh = s ᵥ* B + e - s' ᵥ* G') (hc : c = s ᵥ* (A - P • G) + ec)
    (hy : y = s' ᵥ* Mp + ε) :
    y + Kh ᵥ* X' - c ᵥ* X = P • (s ᵥ* Mp) + (ε + e ᵥ* X' - ec ᵥ* X) := by sorry
