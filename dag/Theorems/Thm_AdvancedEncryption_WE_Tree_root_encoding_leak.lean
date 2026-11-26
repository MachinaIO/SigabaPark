import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem AdvancedEncryption.WE.Tree.root_encoding_leak {K : Type*} [CommRing K] {k n : ℕ}
    (c : Kˣ) (Gm : Matrix (Fin k) (Fin n) K) (Ginv : Matrix (Fin n) (Fin n) K)
    (hG : Gm * Ginv = ((c⁻¹ : Kˣ) : K) • Gm) (s : Fin k → K) (e : Fin n → K) :
    (s ᵥ* ((c : K) • Gm) + e) ᵥ* Ginv = s ᵥ* Gm + e ᵥ* Ginv := by sorry
