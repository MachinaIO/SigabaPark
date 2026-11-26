module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_Fourier
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

variable {B R E : Type*} [Fintype B] [Nonempty B] [DecidableEq B]
variable [Fintype R] [Nonempty R] [AddCommGroup R] [DecidableEq R]
variable [Fintype E] [Sub E] [DecidableEq E]

/-- Joint mass of a block match, a specified remaining-coordinate difference, and
a specified error difference for two independent uniform-coordinate draws. -/
noncomputable def matchedMass (p : E → ℝ) (r : R) (z : E) : ℝ :=
  (∑ i : E, ∑ j : E, if i - j = z then
    ∑ b : B, ∑ y : R, ∑ c : B, if c = b then
      ∑ x : R, if x = r + y then p i * p j else 0
    else 0 else 0) / ((Fintype.card B : ℝ) * Fintype.card R) ^ 2

/-- Normalizing the matching event by its mass yields the product of the uniform
remaining-coordinate mass and the difference law of two independent errors.
The algebraic identity also holds for unnormalized weights. -/
theorem matchedMass_conditional (p : E → ℝ) (r : R) (z : E) :
    matchedMass (B := B) p r z / (1 / (Fintype.card B : ℝ)) =
      (∑ i : E, ∑ j : E, if i - j = z then p i * p j else 0) / Fintype.card R := by
  classical
  unfold matchedMass
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp_rw [← mul_ite_zero, ← Finset.mul_sum]
  have hb : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hr : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- At depth zero, deterministic error one modulo two has unit character magnitude
but negative cosine mean. A positive real mean needs a separate hypothesis. -/
theorem zeroStage_negative_mean :
    |Real.cos (2 * Real.pi * 1 / 2)| = 1 ∧ Real.cos (2 * Real.pi * 1 / 2) = -1 := by
  rw [show 2 * Real.pi * 1 / 2 = Real.pi by ring, Real.cos_pi]
  norm_num

/-- After a fresh difference the real part of the character mean is nonnegative. -/
theorem errorMean_difference_re {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ)
    (e : ι → G) (ψ : G → ℂ) (hψ : ∀ x y, ψ (x - y) = ψ x * star (ψ y)) :
    (∑ i, (p i : ℂ) * ∑ j, (p j : ℂ) * ψ (e i - e j)).re =
      Complex.normSq (∑ i, (p i : ℂ) * ψ (e i)) := by
  change _ = ((Complex.normSq (∑ i, (p i : ℂ) * ψ (e i)) : ℝ) : ℂ).re
  rw [← Complex.mul_conj]
  simp only [hψ, map_sum, map_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]
  conv_lhs => rw [Finset.sum_comm]
  simp only [mul_left_comm]

#print axioms errorMean_difference_re
#print axioms zeroStage_negative_mean
#print axioms matchedMass_conditional

end SigabaNeo.Lattices.Attacks.Bkw
