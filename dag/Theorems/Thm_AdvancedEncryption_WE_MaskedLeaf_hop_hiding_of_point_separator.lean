import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **One-path flip hidden by a point separator.** The positional (PLR) hop of the masked
GGH15 candidate changes the mask carried by a single path `t` (its isolated eq leaf) from `M t`
to `m'`, while every path's value also carries the shared constraint pad `c_z A`. If some `ℓ` has
`c_t ⬝ᵥ ℓ = 1` and `c_z ⬝ᵥ ℓ = 0` for `z ≠ t` (that is, `c_t` is outside the span of the other
path rows), the shift `A ↦ A + ℓ ⊗ (M t − m')` is a bijection between the two views, so for
uniform `A` the flip is perfectly hidden (note `pq-we-masked-overcomplete-leaf`, §11). -/
theorem AdvancedEncryption.WE.MaskedLeaf.hop_hiding_of_point_separator {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ι β : Type*} [DecidableEq ι] [AddCommMonoid β] {k n : ℕ} (c : ι → Fin k → R) (t : ι)
    (ℓ : Fin k → R) (ht : c t ⬝ᵥ ℓ = 1) (ho : ∀ z, z ≠ t → c z ⬝ᵥ ℓ = 0)
    (M : ι → Fin n → R) (m' : Fin n → R) (e : ι → Fin n → R)
    (F : (ι → Fin n → R) → β) :
    ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => M z + c z ᵥ* A + e z) =
      ∑ A : Matrix (Fin k) (Fin n) R,
        F (fun z => Function.update M t m' z + c z ᵥ* A + e z) := by sorry
