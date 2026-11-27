import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

theorem AdvancedEncryption.WE.SplitRank.reencode_rows
    {A B I K : Type} [Fintype I] [Fintype K]
    (u : A → I → ZMod 2) (v : B → I → ZMod 2)
    (coeff : A → K → ZMod 2) (basisRow : K → I → ZMod 2)
    (hu : ∀ a i, u a i = ∑ k, coeff a k * basisRow k i) (a : A) (b : B) :
    dotProduct (u a) (v b) = dotProduct (coeff a) (fun k ↦ dotProduct (basisRow k) (v b)) := by
  sorry
