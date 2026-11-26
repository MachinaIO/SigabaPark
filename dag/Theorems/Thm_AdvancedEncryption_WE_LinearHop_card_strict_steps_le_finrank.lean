import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-- A monotone chain of subspaces `R 0 ≤ R 1 ≤ …` of a finite-dimensional space has at most
`finrank K V` strict steps below any `n`. Counting core of the linear-hop barrier (note
`pq-we-linear-hop-barrier`): `R t` is the span of the shifts applied by the first `t` hops. -/
theorem AdvancedEncryption.WE.LinearHop.card_strict_steps_le_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (R : ℕ → Submodule K V) (hR : Monotone R) (n : ℕ) :
    {t | t < n ∧ R t ≠ R (t + 1)}.ncard ≤ Module.finrank K V := by sorry
