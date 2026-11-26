import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

/-- **Width bound for walks that keep a cut fixed.** Under the hypotheses of
`fixed_rows_linearIndependent`, the number of prefixes at the cut is at most the dimension of the
row space. With the `2^i` witness prefixes at cut `i` this is `2^i ≤ D`, the width lower bound of
note `pq-we-shallow-split-arrangements`. -/
theorem AdvancedEncryption.WE.ShallowSplit.fixed_rows_card_le {K : Type*} [Field K] {V U ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (X : V → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K))
    (h : ∀ x, ∃ t u, L (t + 1) (X x) u ≠ L t (X x) u ∧
      ∀ y, y ≠ x → L (t + 1) (X y) u = L t (X y) u) :
    Fintype.card V ≤ Fintype.card ι := by sorry
