import Definitions.Def_LatticeAttack_Research_Wall1_ThetaProfile
import Definitions.Def_LatticeAttack_Research_Wall1_GaussianSmoothing1D
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit true

/-! Explicit upper bounds for the centered one-dimensional theta factor. -/
noncomputable section
namespace SigabaNeo.Wall1
open Real MeasureTheory

theorem thetaFactor_eq_one_add_tail {a : ℝ} (ha : 0 < a) :
    thetaFactor a = 1 + 2 * tailSum a := by
  let f : ℤ → ℝ := fun k ↦ Real.exp (-a * (k : ℝ)^2)
  have hs : Summable f := summable_int_gauss ha
  have hn : Summable (fun n : ℕ ↦ f (n : ℤ)) := hs.comp_injective Nat.cast_injective
  have hm : Summable (fun n : ℕ ↦ f (-((n : ℤ)+1))) :=
    hs.comp_injective (fun i j h ↦ by simpa using h)
  have hsplit := tsum_of_nat_of_neg_add_one hn hm
  have hneg : (fun n : ℕ ↦ f (-((n : ℤ)+1))) =
      fun n : ℕ ↦ Real.exp (-a*((n:ℝ)+1)^2) := by
    funext n
    simp only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq]
  have hshift : (∑' n : ℕ, f (n : ℤ)) = 1 + tailSum a := by
    simpa [f, tailSum] using hn.tsum_eq_zero_add
  change (∑' k, f k) = _
  rw [hsplit, hneg, hshift]
  change (1 + tailSum a) + tailSum a = _
  ring

theorem thetaFactor_le_geometric {a : ℝ} (ha : 0 < a) :
    thetaFactor a ≤ 1 + 2 * Real.exp (-a) / (1 - Real.exp (-3*a)) := by
  rw [thetaFactor_eq_one_add_tail ha]
  have h := mul_le_mul_of_nonneg_left (tailSum_le ha) (by norm_num : (0:ℝ) ≤ 2)
  simpa only [← mul_div_assoc, add_comm] using add_le_add_left h 1

/-- The integral comparison used for the first two section directions. -/
theorem thetaFactor_le_one_add_sqrt {a : ℝ} (ha : 0 < a) :
    thetaFactor a ≤ 1 + Real.sqrt (Real.pi/a) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ Real.exp (-a*x^2)) (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hsq : x^2 ≤ y^2 := pow_le_pow_left₀ hx hxy 2
    nlinarith
  have hi : IntegrableOn (fun x : ℝ ↦ Real.exp (-a*x^2)) (Set.Ioi 0) :=
    integrableOn_Ioi_exp_neg_mul_sq_iff.mpr ha
  have h := hanti.tsum_add_one_le_integral hi (fun _ _ ↦ (Real.exp_pos _).le)
  rw [integral_gaussian_Ioi] at h
  have ht : tailSum a ≤ Real.sqrt (Real.pi/a)/2 := by
    simpa only [tailSum, Nat.cast_add, Nat.cast_one] using h
  rw [thetaFactor_eq_one_add_tail ha]
  linarith

/-- Poisson reflection in the direct inverse-square parameter. -/
theorem thetaFactor_reflection {a : ℝ} (ha : 0 < a) :
    thetaFactor a = Real.sqrt (Real.pi/a) * thetaFactor (Real.pi^2/a) := by
  let s := Real.sqrt (Real.pi/a)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)
  have hsq : s^2 = Real.pi/a := Real.sq_sqrt (div_pos Real.pi_pos ha).le
  have he : theta1 s 0 = thetaFactor a := by
    unfold theta1 thetaFactor
    apply tsum_congr
    intro n
    rw [add_zero, hsq]
    congr 1
    field_simp [Real.pi_ne_zero, ha.ne']
  have h := theta1_poisson hs 0
  rw [he] at h
  simp only [mul_zero, cos_zero, mul_one, hsq, neg_mul] at h
  rw [h]
  apply congrArg (fun x ↦ s*x)
  unfold thetaFactor
  apply tsum_congr
  intro n
  congr 1
  ring

/-- The reflected geometric bound is useful when the direct parameter is small. -/
theorem thetaFactor_le_reflected_geometric {a : ℝ} (ha : 0 < a) :
    thetaFactor a ≤ Real.sqrt (Real.pi/a) *
      (1 + 2 * Real.exp (-(Real.pi^2/a)) / (1 - Real.exp (-3*(Real.pi^2/a)))) := by
  rw [thetaFactor_reflection ha]
  exact mul_le_mul_of_nonneg_left (thetaFactor_le_geometric (by positivity))
    (Real.sqrt_nonneg _)

end SigabaNeo.Wall1
#print axioms SigabaNeo.Wall1.thetaFactor_le_geometric
#print axioms SigabaNeo.Wall1.thetaFactor_le_one_add_sqrt

#print axioms SigabaNeo.Wall1.thetaFactor_reflection
#print axioms SigabaNeo.Wall1.thetaFactor_le_reflected_geometric
