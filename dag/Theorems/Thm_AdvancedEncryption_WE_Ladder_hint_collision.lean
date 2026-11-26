import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

/-- Hint collision: a key-switching hint and a BGG+ attribute encoding on the same matrix under the same secret differ by a gadget sample of P s - s'. Used in the note `pq-we-ladder-and-homomorphic-prf`. -/
theorem AdvancedEncryption.WE.Ladder.hint_collision {K : Type*} [CommRing K] {n k : ℕ}
    (A G : Matrix (Fin n) (Fin k) K) (s s' : Fin n → K) (P : K) (e ec : Fin k → K)
    (Kh c : Fin k → K)
    (hK : Kh = s ᵥ* A + e - s' ᵥ* G) (hc : c = s ᵥ* (A - P • G) + ec) :
    Kh - c = (P • s - s') ᵥ* G + (e - ec) := by sorry
