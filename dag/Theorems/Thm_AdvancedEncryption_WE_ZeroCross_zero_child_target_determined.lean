import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **Above a zero child the level target is a function of a short hint.** If the slot rows `A`
of a GGH15 level have a square invertible child preimage `D` with small target `A D = E` (a zero
program entry), then every level target `Y = S A + E'` of those rows equals
`(S E + E' D) D⁻¹`. With `D` public, `Y` carries no information beyond the short matrix
`H = S E + E' D`: the LWE sample is the hint itself, so no hinted-LWE statement can make `Y`
uniform while the zero child stays a zero (note `pq-we-zero-entry-crossing`, §4). -/
theorem AdvancedEncryption.WE.ZeroCross.zero_child_target_determined {R ι μ ν : Type*} [CommRing R] [Fintype ι] [Fintype μ] [DecidableEq μ]
    (S : Matrix ν ι R) (A : Matrix ι μ R) (D Dinv : Matrix μ μ R) (E : Matrix ι μ R)
    (E' : Matrix ν μ R) (hA : A * D = E) (hD : D * Dinv = 1) :
    S * A + E' = (S * E + E' * D) * Dinv := by sorry
