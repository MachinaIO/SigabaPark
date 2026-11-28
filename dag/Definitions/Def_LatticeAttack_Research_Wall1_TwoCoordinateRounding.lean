import Definitions.Def_LatticeAttack_Research_Wall1_PlanarDiskLower
import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateResidual

set_option autoImplicit true

/-! # Expected completion residual after product rounding

This is a pointwise scalar bound. Converting it to an integer-ball count still
requires planar completion counts and the tent-kernel integration argument.
-/

noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset TwoCoordinateResidual

/-- Leave two coordinates for completion after rounding the first `n` coordinates. -/
theorem rounding_residual_lower {n : ℕ} (x : Fin n → ℝ) (radiusSq : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    residual c (radiusSq - ((∑ i, (x i)^2) + (n : ℝ)/4)) ≤
      ∑ b, roundingWeight x b *
        residual c (radiusSq - ∑ i, (vertex (x i) (b i) : ℝ)^2) := by
  exact residual_jensen_of_energy_le univ (roundingWeight x)
    (fun b ↦ ∑ i, (vertex (x i) (b i) : ℝ)^2) hc
    (fun b _ ↦ roundingWeight_nonneg x b) (roundingWeight_sum x)
    (roundingWeight_energy_le x)

/-- The scalar Jensen bound controls the actual weighted planar completion count,
including rounded prefixes with negative remaining squared radius. -/
theorem rounding_completion_lower {n : ℕ} (x : Fin n → ℝ) (radiusSq : ℝ) :
    Real.pi * residual (1 / Real.sqrt 2)
      (radiusSq - ((∑ i, (x i)^2) + (n : ℝ)/4)) ≤
      ∑ b, roundingWeight x b *
        (planarCompletions (radiusSq - ∑ i, (vertex (x i) (b i) : ℝ)^2)).card := by
  have h := mul_le_mul_of_nonneg_left
    (rounding_residual_lower x radiusSq (c := 1 / Real.sqrt 2) (by positivity))
    Real.pi_nonneg
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  calc
    _ = roundingWeight x b * (Real.pi * residual (1 / Real.sqrt 2)
        (radiusSq - ∑ i, (vertex (x i) (b i) : ℝ)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (planarCompletions_lower _)
      (roundingWeight_nonneg x b)

end SigabaNeo.Wall1.RawBallRounding

#print axioms SigabaNeo.Wall1.RawBallRounding.rounding_residual_lower

#print axioms SigabaNeo.Wall1.RawBallRounding.rounding_completion_lower
