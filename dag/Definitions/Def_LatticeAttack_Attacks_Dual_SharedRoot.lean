import Definitions.Def_LatticeAttack_Attacks_Dual_FreshMoments

set_option autoImplicit true

namespace SigabaNeo.DualMoments

open MeasureTheory ProbabilityTheory

variable {q m N : ℕ} [NeZero q]

noncomputable def wave (w b : Residues q m) : ℝ := (dotCharacter w b).re

noncomputable def bias (μ : Measure (Residues q m)) (w : Residues q m) : ℝ :=
  ∫ b, wave w b ∂μ

private lemma product_wave (u v b : Residues q m) :
    wave u b * wave v b = (wave (u + v) b + wave (u - v) b) / 2 := by
  simp only [wave, dotCharacter, AddChar.coe_mk, Pi.add_apply, Pi.sub_apply, add_mul,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, ZMod.stdAddChar_apply,
    sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    Complex.mul_re]
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

private lemma wave_icc (w b : Residues q m) : wave w b ∈ Set.Icc (-1) 1 := by
  apply abs_le.mp
  exact (Complex.abs_re_le_norm _).trans (by simp [dotCharacter, ZMod.stdAddChar_apply])

private lemma wave_lp (μ : Measure (Residues q m)) [IsProbabilityMeasure μ]
    (w : Residues q m) : MemLp (wave w) 2 μ := by
  apply memLp_of_bounded (ae_of_all _ (wave_icc w)) (measurable_of_finite _).aestronglyMeasurable

/-- The pairwise spectral condition is evaluated at the actual sum and difference residues. -/
theorem shared_variance (μ : Measure (Residues q m)) [IsProbabilityMeasure μ]
    (w : Fin N → Residues q m) {κ : ℝ} (hk : 0 ≤ κ)
    (hp : ∀ i j, i ≠ j → (bias μ (w i + w j) + bias μ (w i - w j)) / 2
      ≤ bias μ (w i) * bias μ (w j) + κ) :
    variance (fun b ↦ ∑ i, wave (w i) b) μ ≤ N + (N : ℝ)^2 * κ := by
  classical
  rw [variance_fun_sum (fun i ↦ wave_lp μ (w i))]
  have h (i j : Fin N) : covariance (wave (w i)) (wave (w j)) μ ≤
      (if i = j then 1 else 0) + κ := by
    by_cases hij : i = j
    · subst j
      rw [covariance_self (measurable_of_finite _).aemeasurable, ite_eq_left rfl]
      have hv := variance_le_sq_of_bounded (μ := μ) (ae_of_all _ (wave_icc (w i)))
        (measurable_of_finite _).aemeasurable
      norm_num at hv
      linarith
    · rw [covariance_eq_sub (wave_lp ..) (wave_lp ..), ite_eq_right hij, zero_add]
      simp_rw [Pi.mul_def, product_wave]
      rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]
      exact sub_le_iff_le_add.mpr (by simpa [bias, add_comm] using hp i j hij)
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h i j
    _ = _ := by simp [Finset.sum_add_distrib]; ring

private lemma uniform_bias (U : Measure (Residues q m)) [IsProbabilityMeasure U]
    (hU : ∀ b, U.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    (w : Residues q m) (hw : w ≠ 0) : bias U w = 0 := by
  rw [bias, integral_fintype Integrable.of_finite]
  simpa [hU, wave, moment] using uniform_character_mean w hw

/-- Half-mean threshold test on one RHS with a fixed admissible tuple of kernel directions. -/
theorem shared_dual_test {n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Residues q n)
    (E U : Measure (Residues q m)) [IsProbabilityMeasure E] [IsProbabilityMeasure U]
    (hU : ∀ b, U.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    (w : Fin N → Residues q m) (hker : ∀ i, Matrix.vecMul (w i) A = 0)
    (hnz : ∀ i, w i ≠ 0) (hsep : ∀ i j, i ≠ j → w i + w j ≠ 0 ∧ w i - w j ≠ 0)
    {ε κ : ℝ} (hn : 0 < N) (he : 0 < ε) (hk : 0 ≤ κ) (hb : ∀ i, ε ≤ bias E (w i))
    (hp : ∀ i j, i ≠ j → (bias E (w i + w j) + bias E (w i - w j)) / 2
      ≤ bias E (w i) * bias E (w j) + κ) :
    let accept := fun (b : Residues q m) ↦ N * ε / 2 ≤ ∑ i, wave (w i) b
    1 - (2 * N + (N : ℝ)^2 * κ) / (N * ε / 2)^2 ≤
      E.real {e | accept (A.mulVec s + e)} - U.real {b | accept b} := by
  classical
  let S := fun b ↦ ∑ i, wave (w i) b
  let t : ℝ := N * ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hz := uniform_bias U hU
  have vu : variance S U ≤ N := by
    simpa [S] using shared_variance U w (κ := 0) le_rfl (fun i j hij ↦ by
      simp [hz _ (hsep i j hij).1, hz _ (hsep i j hij).2, hz _ (hnz i)])
  have ve := shared_variance E w hk hp
  have mu : ∫ b, S b ∂U = 0 := by
    dsimp [S]
    rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
    exact Finset.sum_eq_zero fun i _ ↦ hz _ (hnz i)
  have me : N * ε ≤ ∫ b, S b ∂E := by
    simpa [S, integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite), bias] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hb i)
  have tail (μ : Measure (Residues q m)) [IsProbabilityMeasure μ] :
      μ.real {b | t ≤ |S b - ∫ z, S z ∂μ|} ≤ variance S μ / t^2 := by
    simpa [Measure.real, ENNReal.toReal_ofReal (div_nonneg (variance_nonneg ..) (sq_nonneg _))]
      using ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (meas_ge_le_variance_div_sq (μ := μ) (X := S) (memLp_finsetSum _ (fun i _ ↦ wave_lp μ (w i))) ht)
  let D := {b | t ≤ S b}
  have u : U.real D ≤ N / t^2 := by
    refine (measureReal_mono (s₂ := {b | t ≤ |S b - ∫ z, S z ∂U|}) ?_).trans
      ((tail U).trans (div_le_div_of_nonneg_right vu (sq_nonneg _)))
    intro b h
    simpa [mu] using le_trans h (le_abs_self (S b))
  have e : E.real Dᶜ ≤ (N + (N : ℝ)^2 * κ) / t^2 := by
    refine (measureReal_mono (s₂ := {b | t ≤ |S b - ∫ z, S z ∂E|}) ?_).trans
      ((tail E).trans (div_le_div_of_nonneg_right ve (sq_nonneg _)))
    intro b h
    change ¬ t ≤ S b at h
    change t ≤ |S b - ∫ z, S z ∂E|
    apply le_trans _ (neg_le_abs _)
    dsimp [t] at *
    linarith
  rw [measureReal_compl (MeasurableSet.of_discrete), probReal_univ] at e
  dsimp only
  simp only [wave, kernel_phase A _ _ s (hker _)]
  change 1 - _ / t^2 ≤ E.real D - U.real D
  linarith [show (2 * (N : ℝ) + N^2 * κ) / t^2 =
    (N + (N : ℝ)^2 * κ) / t^2 + N / t^2 by ring]

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.shared_variance
#print axioms SigabaNeo.DualMoments.shared_dual_test
