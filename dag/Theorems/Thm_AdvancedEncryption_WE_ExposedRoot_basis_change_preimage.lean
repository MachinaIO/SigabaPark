import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **Exposed-row basis change (note `pq-we-exposed-root-reachable-lemma`, §2).** A GGH15
preimage `D ← A⁻¹(Y)` is a Gaussian on the coset `{D : A D = Y}`. For an invertible row
transformation `W = [V; P']` (exposed rows `V`, complement `P'`) this coset equals
`{D : (W A) D = W Y}`, so sampling in the transformed basis is the same distribution, exactly.
This is the decomposition step of the reachable-space Lemma 4.4. -/
theorem AdvancedEncryption.WE.ExposedRoot.basis_change_preimage {R : Type*} [Ring R] {n m k : Type*}
    [Fintype n] [DecidableEq n] [Fintype m]
    (W Winv : Matrix n n R) (hW : Winv * W = 1)
    (A : Matrix n m R) (D : Matrix m k R) (Y : Matrix n k R) :
    A * D = Y ↔ (W * A) * D = W * Y := by sorry
