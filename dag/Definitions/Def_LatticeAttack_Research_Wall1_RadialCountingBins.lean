import Definitions.Def_LatticeAttack_Research_Wall1_TerminalMajorant506
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit true

/-! # Finite radial bins and their frequency kernel

At bounded energy only finitely many bins are needed. The triangular cosine integral is
the even real form of the Fourier representation used in Part 161.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Real MeasureTheory

theorem sinc_sq_triangle (u : ℝ) :
    sinc (4*u)^2 = (1/4) * ∫ t in (0:ℝ)..8, (1-t/8)*cos (t*u) := by
  by_cases hu : u = 0
  · subst u
    simp only [mul_zero, sinc_zero, one_pow, cos_zero, mul_one]
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_div, integral_id, intervalIntegral.integral_const]
    norm_num
  let P (t : ℝ) := (1-t/8)*sin (t*u)/u - cos (t*u)/(8*u^2)
  have hP (t : ℝ) : HasDerivAt P ((1-t/8)*cos (t*u)) t := by
    have ht := (hasDerivAt_id t).mul_const u
    have h := ((((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const 8)).mul
      ht.sin).div_const u).sub (ht.cos.div_const (8*u^2))
    apply h.congr_deriv
    dsimp
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hP t) (by apply Continuous.intervalIntegrable; fun_prop),
    sinc_of_ne_zero (mul_ne_zero (by norm_num) hu)]
  simp only [P, div_self (by norm_num : (8:ℝ) ≠ 0), sub_self, zero_mul, zero_div, zero_sub,
    sub_zero, sin_zero, cos_zero, mul_zero]
  rw [show 8*u = 2*(4*u) by ring, Real.cos_two_mul]
  field_simp
  nlinarith [sin_sq_add_cos_sq (4*u)]

private theorem sin_one_le_sinc {y : ℝ} (hy : |y| ≤ 1) : sin 1 ≤ sinc y := by
  have pos (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : sin 1 ≤ sinc x := by
    rcases h0.eq_or_lt with h | h
    · rw [← h, sinc_zero]
      exact sin_le_one _
    rw [sinc_of_ne_zero h.ne', le_div_iff₀ h]
    have H := strictConcaveOn_sin_Icc.concaveOn.2
      (show (0:ℝ) ∈ Set.Icc 0 π by simp [Real.pi_pos.le])
      (show (1:ℝ) ∈ Set.Icc 0 π by exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩)
      (sub_nonneg.mpr h1) h.le (by ring : 1-x+x=1)
    simpa [smul_eq_mul, mul_comm] using H
  rcases le_or_gt 0 y with h | h
  · exact pos y h (abs_of_nonneg h ▸ hy)
  · rw [← sinc_neg]
    exact pos _ (by linarith) (abs_of_neg h ▸ hy)

/-- For energy X in [0,n/2), one of the n bins already pays the full indicator. -/
theorem radial_bin_majorization {X : ℝ} {n : ℕ} (hX : 0 ≤ X) (hn : 2*X < n) :
    sin 1 ^ 2 ≤ ∑ j ∈ Finset.range n, exp (X-(j:ℝ)/2) *
      sinc (4*(X-((j:ℝ)+1/2)/2))^2 := by
  let j := ⌊2*X⌋₊
  have hj : j < n := (Nat.floor_lt (by positivity)).mpr hn
  have hl : (j:ℝ) ≤ 2*X := Nat.floor_le (by positivity)
  have hr : 2*X < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hsin := sin_one_le_sinc (y := 4*(X-((j:ℝ)+1/2)/2)) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have he : 1 ≤ exp (X-(j:ℝ)/2) := Real.one_le_exp (by linarith)
  calc
    _ ≤ sinc (4*(X-((j:ℝ)+1/2)/2))^2 := pow_le_pow_left₀
      (sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])) hsin 2
    _ ≤ exp (X-(j:ℝ)/2) * _ := le_mul_of_one_le_left (sq_nonneg _) he
    _ ≤ _ := Finset.single_le_sum (f := fun k : ℕ ↦ exp (X-(k:ℝ)/2) *
      sinc (4*(X-((k:ℝ)+1/2)/2))^2) (fun k _ ↦ by positivity) (Finset.mem_range.mpr hj)


/-- A single radial bin, summed over a countable weighted set. Absolute convergence justifies
interchanging the frequency integral and the point sum before the triangle inequality. -/
theorem sinc_mass_le_frequency_integral {ι : Type*} [Countable ι] (w e : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (c : ℝ) :
    (∑' i, w i * sinc (4*(e i-c))^2) ≤ (1/4) *
      ∫ t in (0:ℝ)..8, (1-t/8) *
        ‖∑' i, (w i : ℂ) * Complex.exp ((t*e i : ℝ) * Complex.I)‖ := by
  let μ := volume.restrict (Set.Ioc (0:ℝ) 8)
  let P (i : ι) (t : ℝ) : ℂ := (w i : ℂ) * Complex.exp ((t*e i : ℝ)*Complex.I)
  let F (i : ι) (t : ℝ) := (1-t/8) * (w i*cos (t*(e i-c)))
  have hn (i : ι) (t : ℝ) : ‖P i t‖ = w i := by
    simp only [P, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hw i), mul_one]
  have hP (t : ℝ) : Summable (fun i ↦ P i t) :=
    hs.of_norm_bounded (fun i ↦ (hn i t).le)
  have hPc : Continuous (fun t ↦ ∑' i, P i t) := continuous_tsum
    (fun i ↦ by dsimp [P]; fun_prop) hs (fun i t ↦ (hn i t).le)
  have hFc (i : ι) : Continuous (F i) := by dsimp [F]; fun_prop
  have hFi (i : ι) : Integrable (F i) μ := (hFc i).integrableOn_Ioc
  have ht : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0:ℝ) 8 := ae_restrict_mem measurableSet_Ioc
  have hbound (i : ι) : ∀ᵐ t ∂μ, ‖F i t‖ ≤ w i := by
    filter_upwards [ht] with t ht
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    calc
      _ ≤ 1 * (w i * 1) := by
        apply mul_le_mul _ (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (hw i))
          (mul_nonneg (hw i) (abs_nonneg _)) zero_le_one
        apply abs_le.mpr
        constructor <;> linarith [ht.1, ht.2]
      _ = _ := by ring
  have he : (∑' i, ∫ t, F i t ∂μ) = ∫ t, ∑' i, F i t ∂μ := by
    apply integral_tsum_of_summable_integral_norm hFi
    apply Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) _
      (hs.mul_left (μ.real Set.univ))
    intro i
    simpa [smul_eq_mul] using integral_mono_ae (hFi i).norm
      (integrable_const (w i)) (hbound i)
  have hu : (0:ℝ) ≤ 8 := by norm_num
  have hbin (i : ι) : w i * sinc (4*(e i-c))^2 = (1/4) * ∫ t, F i t ∂μ := by
    rw [sinc_sq_triangle, intervalIntegral.integral_of_le hu, mul_left_comm,
      ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t ↦ by dsimp [F]; ring
  simp_rw [hbin, tsum_mul_left, he, intervalIntegral.integral_of_le hu]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hcos : Continuous (fun t ↦ ∑' i, w i * cos (t*(e i-c))) := by
    apply continuous_tsum (fun i ↦ by fun_prop) hs
    intro i t
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)] using
      mul_le_mul_of_nonneg_left (abs_cos_le_one (t*(e i-c))) (hw i)
  simp only [F, tsum_mul_left]
  apply integral_mono_ae ((continuous_const.sub (continuous_id.div_const 8)).mul hcos).integrableOn_Ioc
    ((continuous_const.sub (continuous_id.div_const 8)).mul hPc.norm).integrableOn_Ioc
  filter_upwards [ht] with t ht
  apply mul_le_mul_of_nonneg_left _ (by change 0 ≤ 1-t/8; linarith [ht.2])
  let phase := Complex.exp ((-(t*c) : ℝ)*Complex.I)
  have hphase : ‖phase‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  calc
    _ = (phase * ∑' i, P i t).re := by
      rw [← tsum_mul_left, Complex.re_tsum ((hP t).mul_left _)]
      apply tsum_congr
      intro i
      have harg : ((-(t*c) : ℝ) : ℂ)*Complex.I + ((t*e i : ℝ) : ℂ)*Complex.I =
          ((t*(e i-c) : ℝ) : ℂ)*Complex.I := by push_cast; ring
      simp only [phase, P, mul_left_comm phase, ← Complex.exp_add, harg]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    _ ≤ _ := (Complex.re_le_norm _).trans_eq (by rw [norm_mul, hphase, one_mul])


/-- Count a finite set whose energies lie in the nonnegative band, by integrating the
absolute characteristic sum of the full exponentially weighted measure. -/
theorem count_le_frequency_integral {ι : Type*} [Countable ι] (X : ι → ℝ) (A : Finset ι)
    (hs : Summable (fun i ↦ exp (X i))) {n : ℕ}
    (hA : ∀ i ∈ A, 0 ≤ X i ∧ 2*X i < n) :
    (A.card : ℝ) * sin 1^2 ≤ ((1/4)/(1-exp (-(1/2)))) *
      ∫ t in (0:ℝ)..8, (1-t/8) *
        ‖∑' i, (exp (X i) : ℂ) * Complex.exp ((t*X i : ℝ) * Complex.I)‖ := by
  let k (j : ℕ) (i : ι) := exp (X i) * sinc (4*(X i-((j:ℝ)+1/2)/2))^2
  let I := ∫ t in (0:ℝ)..8, (1-t/8) *
    ‖∑' i, (exp (X i) : ℂ) * Complex.exp ((t*X i : ℝ) * Complex.I)‖
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) fun t ht ↦
    mul_nonneg (by linarith [ht.2]) (norm_nonneg _)
  have hk (j : ℕ) : Summable (k j) := by
    apply Summable.of_nonneg_of_le (fun i ↦ by dsimp [k]; positivity) _ hs
    intro i
    apply mul_le_of_le_one_right (exp_pos _).le
    exact (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
  have hrow (j : ℕ) : ∑ i ∈ A, k j i ≤ (1/4)*I :=
    ((hk j).sum_le_tsum A (fun i _ ↦ by dsimp [k]; positivity)).trans
      (sinc_mass_le_frequency_integral (fun i ↦ exp (X i)) X (fun i ↦ (exp_pos _).le) hs
        (((j:ℝ)+1/2)/2))
  let a := exp (-(1/2))
  have ha : a < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have geom : ∑ j ∈ Finset.range n, a^j ≤ (1-a)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (exp_pos _).le ha]
    exact (summable_geometric_of_lt_one (exp_pos _).le ha).sum_le_tsum _ (by
      intro i hi; positivity)
  calc
    _ = ∑ i ∈ A, sin 1^2 := by simp
    _ ≤ ∑ i ∈ A, ∑ j ∈ Finset.range n, a^j * k j i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (radial_bin_majorization (hA i hi).1 (hA i hi).2).trans_eq
      apply Finset.sum_congr rfl
      intro j _
      have he : X i - (j:ℝ)/2 = (j:ℕ)*(-(1/2):ℝ) + X i := by ring
      rw [he, Real.exp_add, Real.exp_nat_mul]
      dsimp only [a,k]
      ring
    _ = ∑ j ∈ Finset.range n, a^j * ∑ i ∈ A, k j i := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range n, a^j * ((1/4)*I) := Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (hrow j) (pow_nonneg (exp_pos _).le _)
    _ = (∑ j ∈ Finset.range n, a^j) * ((1/4)*I) := (Finset.sum_mul ..).symm
    _ ≤ (1-a)⁻¹ * ((1/4)*I) := mul_le_mul_of_nonneg_right geom (by positivity)
    _ = _ := by change _ = ((1/4)/(1-a))*I; ring

private theorem theta_pos {u : ℝ} (hu : 0 < u) : 0 < terminalTheta u := by
  have h : Real.exp (-3*Real.pi*u^2) < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (sq_pos_of_pos hu))
  unfold terminalTheta
  positivity

private theorem theta_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    terminalTheta v ≤ terminalTheta u := by
  have hs := pow_le_pow_left₀ hu.le huv 2
  have h : exp (-3*π*u^2) < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (sq_pos_of_pos hu))
  unfold terminalTheta
  apply add_le_add_right
  apply div_le_div₀ (by positivity) _ (sub_pos.mpr h) _
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hs (by linarith [pi_pos])
  · apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hs (by linarith [pi_pos])

/-- The integral of any frequency density bounded by the Part 161 envelope is controlled by
the same right- and left-endpoint sum that occurs in countingConstantAt. -/
theorem frequency_integral_le_bins {z : ℝ} (hz : 0 < z) (F : ℝ → ℝ)
    (hcont : Continuous F)
    (hF : ∀ t ∈ Set.Icc (0:ℝ) 8, F t ≤
      (1-t/8)*(1+t^2)^(-(506/4):ℝ)*terminalTheta (z/sqrt (1+t^2))^506) :
    (∫ t in (0:ℝ)..8, F t) ≤ ∑ j ∈ Finset.range 4096,
      let x := (j:ℝ)/512
      let y := ((j:ℝ)+1)/512
      (1/512)*(1-x/8)*(1+x^2)^(-(506/4):ℝ)*terminalTheta (z/sqrt (1+y^2))^506 := by
  let a (i : ℕ) : ℝ := (i:ℝ)/512
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := 4096)
    (fun _ _ ↦ hcont.intervalIntegrable _ _ (μ := volume))
  rw [show a 0 = 0 by norm_num [a], show a 4096 = 8 by norm_num [a]] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro j hj
  let x := a j
  let y := a (j+1)
  let B := (1-x/8)*(1+x^2)^(-(506/4):ℝ)*terminalTheta (z/sqrt (1+y^2))^506
  have hx : 0 ≤ x := by dsimp [x,a]; positivity
  have hy : y ≤ 8 := by
    have hh : (j:ℝ)+1 ≤ 4096 := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    dsimp [y,a]; push_cast; linarith
  have hxy : y-x = 1/512 := by dsimp [x,y,a]; push_cast; ring
  have hi : x ≤ y := by linarith
  have hb (t : ℝ) (ht : t ∈ Set.Icc x y) : F t ≤ B := by
    have ht0 := hx.trans ht.1
    have ht8 := ht.2.trans hy
    apply (hF t ⟨ht0, ht8⟩).trans
    apply mul_le_mul _ _ (by positivity) (by apply mul_nonneg _ (by positivity); linarith)
    · apply mul_le_mul (by linarith [ht.1]) _ (by positivity) (by linarith)
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
      gcongr
      exact ht.1
    · apply pow_le_pow_left₀ (theta_pos (by positivity)).le
      apply theta_antitone (by positivity)
      apply div_le_div_of_nonneg_left hz.le (by positivity)
      gcongr
      exact ht.2
  have h := intervalIntegral.integral_mono_on hi (hcont.intervalIntegrable _ _ (μ := volume))
    (intervalIntegrable_const (c := B)) hb
  rw [intervalIntegral.integral_const, hxy, smul_eq_mul] at h
  refine h.trans_eq ?_
  dsimp [B,x,y,a]
  push_cast
  ring

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.sinc_sq_triangle
#print axioms SigabaNeo.Wall1.TerminalProjection.radial_bin_majorization

#print axioms SigabaNeo.Wall1.TerminalProjection.frequency_integral_le_bins
#print axioms SigabaNeo.Wall1.TerminalProjection.sinc_mass_le_frequency_integral

#print axioms SigabaNeo.Wall1.TerminalProjection.count_le_frequency_integral
