import Definitions.Def_LatticeAttack_Attacks_Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit true

/-! Finite-law signed cosine bounds and a shared binary phase. -/

namespace SigabaNeo.DualMoments

/-- The weighted second moment of the unwrapped phase controls its signed cosine mean. -/
theorem phase_second_moment_bias {Ω : Type*} [Fintype Ω] (p θ : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hn : ∑ x, p x = 1) :
    1 - moment p (fun x ↦ θ x ^ 2) / 2 ≤ moment p (fun x ↦ Real.cos (θ x)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦
    mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := θ x)) (hp x))
  simpa [moment, mul_sub, div_eq_mul_inv, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul, hn] using h

/-- A support bound on the absolute inner product gives an explicit signed bias.
The finite sample space may encode both the direction and the error. -/
theorem bounded_inner_product_bias {Ω : Type*} [Fintype Ω] (p d : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hn : ∑ x, p x = 1) {B q : ℝ}
    (hd : ∀ x, p x ≠ 0 → |d x| ≤ B) :
    1 - ((2 * Real.pi / q) * B) ^ 2 / 2 ≤
      moment p (fun x ↦ Real.cos ((2 * Real.pi / q) * d x)) := by
  apply le_trans _ (phase_second_moment_bias p _ hp hn)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ show
      p x * ((2 * Real.pi / q) * d x) ^ 2 ≤ p x * ((2 * Real.pi / q) * B) ^ 2 by
    by_cases hz : p x = 0
    · simp [hz]
    · apply mul_le_mul_of_nonneg_left _ (hp x)
      simp only [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa using pow_le_pow_left₀ (abs_nonneg (d x)) (hd x hz) 2)
  rw [← Finset.sum_mul, hn, one_mul] at h
  unfold moment
  linarith

/-- One uniform bit and repeated nonzero binary direction 1 give variance N². -/
theorem shared_binary_variance (N : ℕ) :
    let p := fun _ : Bool ↦ (1 / 2 : ℝ)
    let X := score (fun _ : Fin N ↦ fun b : Bool ↦ if b then Real.pi else 0)
    moment p (fun b ↦ (X b - moment p X) ^ 2) = (N : ℝ) ^ 2 := by
  dsimp only
  rw [repeated_score_variance]
  norm_num [moment, Fintype.sum_bool]

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.phase_second_moment_bias
#print axioms SigabaNeo.DualMoments.bounded_inner_product_bias
#print axioms SigabaNeo.DualMoments.shared_binary_variance
