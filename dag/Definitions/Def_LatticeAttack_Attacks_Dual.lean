import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit true

/-! Finite moment identities for cosine scores evaluated on a common random input. -/

namespace SigabaNeo.DualMoments

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

noncomputable def moment (p X : Ω → ℝ) : ℝ := ∑ x, p x * X x

noncomputable def score (θ : I → Ω → ℝ) (x : Ω) : ℝ := ∑ i, Real.cos (θ i x)

theorem moment_score (p : Ω → ℝ) (θ : I → Ω → ℝ) :
    moment p (score θ) = ∑ i, moment p (fun x ↦ Real.cos (θ i x)) := by
  simp only [moment, score, Finset.mul_sum]
  exact Finset.sum_comm

theorem moment_score_sq (p : Ω → ℝ) (θ : I → Ω → ℝ) :
    moment p (fun x ↦ score θ x ^ 2) =
      ∑ i, ∑ j, moment p (fun x ↦
        (Real.cos (θ i x + θ j x) + Real.cos (θ i x - θ j x)) / 2) := by
  have h (a b : ℝ) : (Real.cos (a + b) + Real.cos (a - b)) / 2 =
      Real.cos a * Real.cos b := by
    rw [Real.cos_add, Real.cos_sub]
    ring
  simp only [h, moment, score, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset I))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset I))]
  simp only [mul_comm (Real.cos (θ i _))]

/-- Repetitions of a phase multiply its centered second moment by the square of the count. -/
theorem repeated_score_variance (p φ : Ω → ℝ) (n : ℕ) :
    let X := score (fun _ : Fin n ↦ φ)
    moment p (fun x ↦ (X x - moment p X) ^ 2) =
      (n : ℝ) ^ 2 * moment p (fun x ↦
        (Real.cos (φ x) - moment p (fun y ↦ Real.cos (φ y))) ^ 2) := by
  dsimp only
  have hm : moment p (score (fun _ : Fin n ↦ φ)) =
      (n : ℝ) * moment p (fun y ↦ Real.cos (φ y)) := by simp [moment_score]
  rw [hm]
  simp only [score, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    moment]
  rw [Finset.mul_sum _ _ ((n : ℝ) ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  ring

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.moment_score
#print axioms SigabaNeo.DualMoments.moment_score_sq
#print axioms SigabaNeo.DualMoments.repeated_score_variance
