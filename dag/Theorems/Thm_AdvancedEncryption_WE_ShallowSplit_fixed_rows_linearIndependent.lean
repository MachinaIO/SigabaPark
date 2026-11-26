import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

/-- **Rows that a walk never changes must be linearly independent.** Rows `X x` (the
encoding's prefix rows at a fixed cut, over a field) stay fixed along a sequence of hybrids
`t = 0, 1, 2, ...`; hybrid `t` reads the residual of prefix `x` (its values on all suffixes `u`) as
the linear image `L t (X x)`. If every prefix `x` has a step `t` and a suffix `u` at which its
residual changes while the residual of every other prefix at `u` stays the same (a prefix-local
flip: one witness candidate, or one ERASE'd subtree below that prefix), then the rows are linearly
independent. Applied at the cut `n_w - s` above all reroutes of depth `≤ s`, this forces width
`≥ 2^(n_w - s)` (note `pq-we-shallow-split-arrangements`). -/
theorem AdvancedEncryption.WE.ShallowSplit.fixed_rows_linearIndependent {K : Type*} [Field K] {V U ι : Type*} [Fintype V] [DecidableEq V]
    (X : V → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K))
    (h : ∀ x, ∃ t u, L (t + 1) (X x) u ≠ L t (X x) u ∧
      ∀ y, y ≠ x → L (t + 1) (X y) u = L t (X y) u) :
    LinearIndependent K X := by sorry
