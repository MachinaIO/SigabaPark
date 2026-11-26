import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination

/-- Rank-metric noise does not grow under base-field linear maps. For a field extension `K / F`, the
rank weight of `e ∈ K^N` is the `F`-dimension of the span of its entries (its support). Applying
any matrix `H` over the base field `F` keeps the support inside the original one, so the rank
weight never increases. Hence the coordinate gadget of `K` over `F` (preimages are `F`-coordinate
expansions) evaluates any `F`-linear map with no noise growth, unlike the Hamming metric
(`AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages`); the noise can then never gate a
decryption, which is gated by exact `F`-linear cancellation alone. Used in the note
`pq-we-exotic-algebraic-structures`. -/
theorem AdvancedEncryption.WE.Exotic.rank_support_mono {F K : Type*} [Field F] [Field K]
    [Algebra F K] {N n : ℕ} (e : Fin N → K) (H : Matrix (Fin N) (Fin n) F) :
    Submodule.span F (Set.range fun j => ∑ i, H i j • e i) ≤ Submodule.span F (Set.range e) ∧
    Module.finrank F (Submodule.span F (Set.range fun j => ∑ i, H i j • e i)) ≤
      Module.finrank F (Submodule.span F (Set.range e)) := by sorry
