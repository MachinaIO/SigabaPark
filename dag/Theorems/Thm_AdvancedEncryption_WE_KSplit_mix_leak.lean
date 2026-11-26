import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

theorem AdvancedEncryption.WE.KSplit.mix_leak {R : Type} [CommRing R] {r c : Type} [Fintype r]
    (s : r → R) (A G : Matrix r c R) (x x' : R) (e e' : c → R) :
    (Matrix.vecMul s (A - x • G) + e) - (Matrix.vecMul s (A - x' • G) + e') =
      (x' - x) • Matrix.vecMul s G + (e - e') := by
  sorry
