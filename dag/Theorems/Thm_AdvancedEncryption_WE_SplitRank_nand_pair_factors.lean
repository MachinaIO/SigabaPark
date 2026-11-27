import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

theorem AdvancedEncryption.WE.SplitRank.nand_pair_factors
    {I J : Type} [Fintype I] [Fintype J]
    (u v : I → ZMod 2) (w z : J → ZMod 2) (a b : Bool)
    (ha : dotProduct u v = if a then 1 else 0)
    (hb : dotProduct w z = if b then 1 else 0) :
    dotProduct (fun p : Option (I × J) ↦ p.elim 1 (fun q ↦ u q.1 * w q.2))
        (fun p ↦ p.elim 1 (fun q ↦ v q.1 * z q.2)) =
      (if !(a && b) then 1 else 0) := by
  sorry
