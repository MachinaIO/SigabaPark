import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

theorem AdvancedEncryption.WE.TwoInput.rect_leak {R : Type} [CommRing R] {r c : Type} [Fintype r]
    (a a' b b' : r → R) (A G : Matrix r c R) (p p' : R) (e1 e2 e3 e4 : c → R) :
    (Matrix.vecMul (a + b) (A - p • G) + e1) - (Matrix.vecMul (a' + b) (A - p' • G) + e2)
      - (Matrix.vecMul (a + b') (A - p • G) + e3) + (Matrix.vecMul (a' + b') (A - p' • G) + e4) =
      (p' - p) • Matrix.vecMul (b - b') G + (e1 - e2 - e3 + e4) := by
  sorry
