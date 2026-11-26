import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **Overcomplete leaf rows have an affine relation.** If the differences `c_z − c_{z₀}` of
the constraint-block path rows span `K^k` (the rows affinely span the space, which is the generic
situation once the number of distinct path rows exceeds the dimension), then `0` is an affine
combination of the `c_z`. Together with `mask_of_affine_relation` this says that in the overcomplete
regime the noiseless projected path values determine the mask (note
`pq-we-masked-overcomplete-leaf`). -/
theorem AdvancedEncryption.WE.MaskedLeaf.affine_relation_of_span {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k : ℕ}
    (c : ι → Fin k → K) (z₀ : ι)
    (hspan : Submodule.span K (Set.range fun z => c z - c z₀) = ⊤) :
    ∃ α : ι → K, ∑ z, α z = 1 ∧ ∑ z, α z • c z = 0 := by sorry
