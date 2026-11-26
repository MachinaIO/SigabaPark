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

/-- Linear embedding hop dichotomy (note `pq-we-linear-hop-barrier`): if `h ∘ L = 0`, the value
`h (L b + c)` does not depend on the embedded `b`; otherwise, for uniform `u`, `h (L u + c)` is
uniform on `K` (all fibers have the same size). -/
theorem AdvancedEncryption.WE.LinearHop.hop_dichotomy {K U V : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U]
    [Fintype U] [AddCommGroup V] [Module K V] (L : U →ₗ[K] V) (c : V)
    (h : Module.Dual K V) :
    (h.comp L = 0 → ∀ b, h (L b + c) = h c) ∧
    (h.comp L ≠ 0 → ∀ z z' : K,
      {u : U | h (L u + c) = z}.ncard = {u : U | h (L u + c) = z'}.ncard) := by sorry
