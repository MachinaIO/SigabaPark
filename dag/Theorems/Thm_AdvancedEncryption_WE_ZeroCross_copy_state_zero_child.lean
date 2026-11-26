import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **Zero entries are basis-invariant: a copy state creates one.** Suppose two row blocks, a
copy state `a_c` and the main state `a_m`, have children with the same target `T` up to noise:
`a_c D = T + E₁` and `a_m D = T + E₂` (the departure transition of a design that pads a cube with
no zero program entry). Then the difference row has a zero child, `(a_c − a_m) D = E₁ − E₂`. A
design without zero entries in its program has them in the difference basis, and the obstruction
of note `pq-we-zero-entry-crossing` (§6) is unchanged. -/
theorem AdvancedEncryption.WE.ZeroCross.copy_state_zero_child {R ν μ : Type*} [CommRing R] [Fintype μ]
    (ac am : Matrix ν μ R) (D : Matrix μ μ R) (T E1 E2 : Matrix ν μ R)
    (hc : ac * D = T + E1) (hm : am * D = T + E2) :
    (ac - am) * D = E1 - E2 := by sorry
