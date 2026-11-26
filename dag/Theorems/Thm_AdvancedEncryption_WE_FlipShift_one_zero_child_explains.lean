import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **A meeting block with one zero child carries no hidden uniform randomness.** If the block `B`
of a level matrix has the zero child `B D_dep = E_B` with `D_dep` invertible, then
`B = E_B D_dep⁻¹`, and every pad that a prefix row `c` contributes through the other child is
`c (B D_chain F) = (c E_B)(D_dep⁻¹ D_chain F)`: a short row `c E_B` times a public matrix. So the
fat sibling-pad lemma of PR #71 is not an LWE statement with a uniform secret `U = B D_chain`:
conditioned on the public preimages, `U = E_B D_dep⁻¹ D_chain`. -/
theorem AdvancedEncryption.WE.FlipShift.one_zero_child_explains {R : Type*} [CommRing R] {κ μ ν : Type*} [Fintype κ] [Fintype μ] [DecidableEq μ]
    (B E : Matrix κ μ R) (D : Matrix μ μ R) (hD : IsUnit D.det) (hBD : B * D = E) :
    B = E * D⁻¹ ∧ ∀ (c : κ → R) (D' : Matrix μ ν R), c ᵥ* (B * D') = (c ᵥ* E) ᵥ* (D⁻¹ * D') := by sorry
