import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Common

/-- **Generalized fixed-cut lemma (rank form).** Rows `X x` of the prefixes at a cut stay fixed
while hybrids `t` read the residual of `x` (its values on all suffixes `u`) as `L t (X x)`. For
any choice of (step, suffix) columns, the matrix of residual changes `L (t+1) (X x) u - L t (X x) u`
has rank at most the row width. This holds for every layout, read-once or multi-pass (the GGH15
cut factorization does not see which variable a level reads); the prefix-local hypothesis of the
fixed-cut lemma is one way to make this rank large (note `pq-we-multipass-ggh15`). -/
theorem AdvancedEncryption.WE.MultiPass.change_rank_le {K : Type*} [Field K] {V U ι J : Type*} [Fintype V] [Fintype ι] [Fintype J]
    [DecidableEq ι]
    (X : V → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K)) (col : J → ℕ × U) :
    (Matrix.of fun x j => L ((col j).1 + 1) (X x) (col j).2 - L (col j).1 (X x) (col j).2).rank
      ≤ Fintype.card ι := by sorry
