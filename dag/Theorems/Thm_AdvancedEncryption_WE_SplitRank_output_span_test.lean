import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

theorem AdvancedEncryption.WE.SplitRank.output_span_test
    {A B P Q I : Type} [Fintype I]
    (u : A → I → ZMod 2) (v : B → I → ZMod 2)
    (l : P → I → ZMod 2) (r : Q → I → ZMod 2)
    (hl : Submodule.span (ZMod 2) (Set.range u) = Submodule.span (ZMod 2) (Set.range l))
    (hr : Submodule.span (ZMod 2) (Set.range v) = Submodule.span (ZMod 2) (Set.range r)) :
    (∃ a b, dotProduct (u a) (v b) ≠ 0) ↔ ∃ p q, dotProduct (l p) (r q) ≠ 0 := by
  sorry
