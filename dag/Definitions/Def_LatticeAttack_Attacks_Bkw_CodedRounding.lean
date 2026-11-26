module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

set_option autoImplicit true

public section

open Real

namespace SigabaNeo

/-- Uniform mean of the real character on the integer interval from -r to r. -/
noncomputable def centeredCharMean (q : ℕ) [NeZero q] (r : ℕ) (t : ℤ) : ℝ :=
  let I := Finset.Icc (-(r : ℤ)) (r : ℤ)
  (∑ x ∈ I, (ZMod.stdAddChar ((x * t : ℤ) : ZMod q)).re) / I.card

theorem centeredCharMean_lower (q : ℕ) [NeZero q] (r : ℕ) (t : ℤ) (T : ℝ)
    (ht : |(t : ℝ)| ≤ T) (hangle : 2 * π * r * T / q < π / 2) :
    0 < Real.cos (2 * π * r * T / q) ∧
      Real.cos (2 * π * r * T / q) ≤ centeredCharMean q r t := by
  have hT := (abs_nonneg (t : ℝ)).trans ht
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ha : 0 ≤ 2 * π * r * T / q := by positivity
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangle⟩, ?_⟩
  let I := Finset.Icc (-(r : ℤ)) (r : ℤ)
  have hI : I.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  apply (le_div_iff₀ (by exact_mod_cast hI.card_pos : 0 < (I.card : ℝ))).mpr
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hx
  have hx' : |(x : ℝ)| ≤ r := abs_le.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩
  rw [ZMod.stdAddChar_coe]
  have he : (2 * (π : ℂ) * Complex.I * ((x * t : ℤ) : ℂ) / q) =
      ((2 * π * x * t / q : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_mul_I, Complex.add_re, Complex.mul_I_re]
  simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_im, neg_zero, add_zero]
  rw [← Real.cos_abs (2 * π * x * t / q)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  simp only [abs_div, abs_mul, abs_of_pos hq, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
  gcongr

open ComplexConjugate

/-- Independent draws in each coordinate. Uniform weights may be included in `f`. -/
theorem paired_product_mean {k : ℕ} {α : Type*} [Fintype α] (f : Fin k → α → ℂ) :
    (∑ x : Fin k → α, ∑ y : Fin k → α,
      (∏ i, f i (x i)) * conj (∏ i, f i (y i))).re =
      ∏ i, ‖∑ a, f i a‖ ^ 2 := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← map_sum, ← Fintype.prod_sum, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_re, norm_prod, ← Finset.prod_pow]

theorem centered_product_lower (q : ℕ) [NeZero q] {k : ℕ} (r : ℕ) (t : Fin k → ℤ) (T : ℝ)
    (ht : ∀ i, |(t i : ℝ)| ≤ T) (hangle : 2 * π * r * T / q < π / 2) :
    let I := Finset.Icc (-(r : ℤ)) (r : ℤ)
    (Real.cos (2 * π * r * T / q) ^ 2) ^ k ≤
      ∏ i, ‖(∑ x ∈ I, ZMod.stdAddChar ((x * t i : ℤ) : ZMod q)) / (I.card : ℂ)‖ ^ 2 := by
  intro I
  conv_lhs => rw [← Finset.card_fin k, ← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · exact fun _ _ ↦ sq_nonneg _
  intro i _
  obtain ⟨hc, hl⟩ := centeredCharMean_lower q r (t i) T (ht i) hangle
  apply pow_le_pow_left₀ hc.le _ 2
  apply le_trans hl
  apply le_trans _ (Complex.re_le_norm _)
  simp [centeredCharMean, I, Complex.div_natCast_re, Complex.re_sum]

#print axioms centered_product_lower
#print axioms paired_product_mean
#print axioms centeredCharMean_lower

end SigabaNeo
