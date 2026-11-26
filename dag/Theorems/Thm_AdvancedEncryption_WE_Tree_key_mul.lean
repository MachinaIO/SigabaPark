import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem AdvancedEncryption.WE.Tree.key_mul {K : Type*} [CommRing K] {k n N : ℕ}
    (Gm : Matrix (Fin k) (Fin n) K) (Z : Matrix (Fin k) (Fin N) K)
    (Mf Mg : Matrix (Fin n) (Fin n) K) (Hf Hg : Matrix (Fin N) (Fin n) K) (f g : K)
    (hf : Gm * Mf - Z * Hf = f • Gm) (hg : Gm * Mg - Z * Hg = g • Gm) :
    Gm * (Mf * Mg) - Z * (Hf * Mg + f • Hg) = (f * g) • Gm := by sorry
