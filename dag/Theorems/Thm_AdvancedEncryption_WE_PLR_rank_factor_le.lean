import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

open Matrix Module

/-- **Rank factorization, upper bound.** In the PLR-hop rank obstruction of positional masked
GGH15 (note `pq-we-plr-hop-rank-and-erase`, §1, on PR #56), the differences
`V'[x,u] = y_{xu} − y_{xu0}` over a rectangle `S × U` of witness paths factor as
`V' = [X | E] · ΔY`, with rows `X_x` (the structured part), error rows `e_x` (`m` columns) and a
matrix `ΔY` of differences of suffix products. Then `rank V' ≤ rank [X | E] ≤ rank X + m`. -/
theorem AdvancedEncryption.WE.PLR.rank_factor_le {K : Type*} [Field K] {S U κ : Type*} [Fintype U] [Fintype κ] {m : ℕ}
    (X : Matrix S κ K) (E : Matrix S (Fin m) K) (ΔY : Matrix (κ ⊕ Fin m) U K) :
    (fromCols X E * ΔY).rank ≤ (fromCols X E).rank ∧ (fromCols X E).rank ≤ X.rank + m := by sorry
