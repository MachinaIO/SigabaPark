import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

open Matrix Module

/-- **Rank factorization, exact equality.** Same setting as `rank_factor_le` (note
`pq-we-plr-hop-rank-and-erase`, §1, on PR #56): `V' = [X | E] · ΔY`. If `ΔY` has full row rank,
then `rank V' = rank X + m` holds **exactly** when the error block `E` has full column rank `m`
and its column space meets the column space of `X` only in `0`. This pins down the hypotheses
behind the informal claim `rank V' = m + rank{X_x}`. -/
theorem AdvancedEncryption.WE.PLR.rank_factor_eq_iff {K : Type*} [Field K] {S U κ : Type*} [Fintype S] [Fintype U] [Fintype κ]
    {m : ℕ} (X : Matrix S κ K) (E : Matrix S (Fin m) K) (ΔY : Matrix (κ ⊕ Fin m) U K)
    (hY : ΔY.rank = Fintype.card κ + m) :
    (fromCols X E * ΔY).rank = X.rank + m ↔
      E.rank = m ∧ Disjoint (LinearMap.range X.mulVecLin) (LinearMap.range E.mulVecLin) := by sorry
