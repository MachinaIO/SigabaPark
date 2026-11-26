import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **An affine relation reveals the mask.** If the constraint-block rows `c_z` of the paths
satisfy an affine relation `∑ α_z = 1`, `∑ α_z c_z = 0`, then the same combination of the noiseless
path values `m + c_z A` is the mask `m`, whatever the leaf matrix `A`. With noise the combination
gives `m + ∑ α_z e_z`, which is useless to an adversary only when the `α_z` are large. So once the
path rows affinely span (the overcomplete regime) the mask is determined information-theoretically by
the noiseless projections, and no proof can end with a statistical step on them (note
`pq-we-masked-overcomplete-leaf`). -/
theorem AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k n : ℕ}
    (c : ι → Fin k → R) (α : ι → R) (hα : ∑ z, α z = 1) (hrel : ∑ z, α z • c z = 0)
    (m : Fin n → R) (A : Matrix (Fin k) (Fin n) R) :
    ∑ z, α z • (m + c z ᵥ* A) = m := by sorry
