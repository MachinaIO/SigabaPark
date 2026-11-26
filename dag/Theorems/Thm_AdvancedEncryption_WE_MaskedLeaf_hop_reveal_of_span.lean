import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **A path row in the span of the others pins its mask.** If `c_t = ∑ β_z c_z` (meaningful
with `β_t = 0`), the combination `y_t − ∑ β_z y_z` of the path values removes the shared pad
exactly and leaves `M t − ∑ β_z M_z` plus the combined noise. So in the overcomplete regime, where
every path row is in the span of the others, the noiseless values determine the one-path flip of
the positional (PLR) hop. The hop must then be argued computationally from the noise
(note `pq-we-masked-overcomplete-leaf`, §11). -/
theorem AdvancedEncryption.WE.MaskedLeaf.hop_reveal_of_span {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k n : ℕ}
    (c : ι → Fin k → R) (t : ι) (β : ι → R)
    (hrel : c t = ∑ z, β z • c z) (M : ι → Fin n → R) (e : ι → Fin n → R)
    (A : Matrix (Fin k) (Fin n) R) :
    (M t + c t ᵥ* A + e t) - ∑ z, β z • (M z + c z ᵥ* A + e z) =
      (M t - ∑ z, β z • M z) + (e t - ∑ z, β z • e z) := by sorry
