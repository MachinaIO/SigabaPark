import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Common

/-- **Triangular fixed-cut lemma.** The fixed-cut lemma with the prefix-local hypothesis weakened
to a triangular one: prefix `a` has a column `(t a, u a)` at which its residual changes, and the
flips of *later* prefixes may also change the residuals of other prefixes there, but no *earlier*
prefix `a' < a` changes there. Then the number of such prefixes is at most the width. In a
multi-pass layout this covers walks in which a flip also drags along the mixed strings of
prefixes that are flipped later (note `pq-we-multipass-ggh15`). -/
theorem AdvancedEncryption.WE.MultiPass.triangular_card_le {K : Type*} [Field K] {U ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (Y : Fin m → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K)) (t : Fin m → ℕ) (u : Fin m → U)
    (hdiag : ∀ a, L (t a + 1) (Y a) (u a) ≠ L (t a) (Y a) (u a))
    (htri : ∀ a b, a < b → L (t b + 1) (Y a) (u b) = L (t b) (Y a) (u b)) :
    m ≤ Fintype.card ι := by sorry
