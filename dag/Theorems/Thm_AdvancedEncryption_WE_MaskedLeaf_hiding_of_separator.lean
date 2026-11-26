import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **A leaf separator hides the mask perfectly.** In the masked γ⊗-GGH15 candidate, after the
root-first projection steps the leaf constraint matrix `A` (uniform, used nowhere else) enters the
view only through the path values `m + c_z A + e_z`, where `m` is the mask and `c_z` the
constraint-block row of path `z`. If some `ℓ` has `c_z ⬝ᵥ ℓ = 1` on every path (a *separator*),
then the shift `A ↦ A + ℓ ⊗ (m − m')` is a bijection that turns the values for mask `m` into those
for `m'`, so for uniform `A` the law of all path values (with any noise independent of `A`) is the
same for every mask. Stated as an equality of sums over `A` of an arbitrary test function `F`
(note `pq-we-masked-overcomplete-leaf`). -/
theorem AdvancedEncryption.WE.MaskedLeaf.hiding_of_separator {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ι β : Type*} [AddCommMonoid β] {k n : ℕ} (c : ι → Fin k → R) (ℓ : Fin k → R)
    (hℓ : ∀ z, c z ⬝ᵥ ℓ = 1) (m m' : Fin n → R) (e : ι → Fin n → R)
    (F : (ι → Fin n → R) → β) :
    ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => m + c z ᵥ* A + e z) =
      ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => m' + c z ᵥ* A + e z) := by sorry
