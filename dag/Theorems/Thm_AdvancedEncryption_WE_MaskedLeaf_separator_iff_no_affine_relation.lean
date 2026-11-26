import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Matrix

/-- **Dichotomy at the leaf.** Over a field, exactly one of the following holds for the
constraint-block path rows `c_z`: a separator `ℓ` with `c_z ⬝ᵥ ℓ = 1` on all paths exists (then
`hiding_of_separator` hides the mask perfectly), or an affine relation `∑ α_z = 1`,
`∑ α_z c_z = 0` exists (then `mask_of_affine_relation` recovers the mask from the noiseless
values). Equivalently, `0` lies outside or inside the affine hull of the `c_z`
(note `pq-we-masked-overcomplete-leaf`). -/
theorem AdvancedEncryption.WE.MaskedLeaf.separator_iff_no_affine_relation {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k : ℕ}
    (c : ι → Fin k → K) :
    (∃ ℓ : Fin k → K, ∀ z, c z ⬝ᵥ ℓ = 1) ↔
      ¬ ∃ α : ι → K, ∑ z, α z = 1 ∧ ∑ z, α z • c z = 0 := by sorry
