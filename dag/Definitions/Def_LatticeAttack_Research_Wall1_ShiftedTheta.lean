module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

open Real Complex Filter Asymptotics

private theorem gaussian_summable {s : ℝ} (hs : 0 < s) :
    Summable (fun k : ℤ ↦ Real.exp (-s * (k : ℝ)^2)) := by
  have h := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((isLittleO_exp_neg_mul_sq_cocompact (a := (s : ℂ)) hs (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)
  simpa [Function.comp_def, Complex.norm_exp, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul] using h.norm

/-- Translating the integer Gaussian by any real shift can only decrease its mass. -/
theorem shiftedTheta_le {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (∑' k : ℤ, Real.exp (-s * ((k : ℝ) + a)^2)) ≤
      ∑' k : ℤ, Real.exp (-s * (k : ℝ)^2) := by
  let t := π / s
  have ht : 0 < t := div_pos pi_pos hs
  have hdiv : -π / t = -s := by dsimp [t]; field_simp
  let term (k : ℤ) := Complex.exp (-π * (t : ℂ) * (k : ℂ)^2 +
    2 * π * (-(I * a)) * k)
  have hn (k : ℤ) : ‖term k‖ = Real.exp (-(π * t) * (k : ℝ)^2) := by
    simp [term, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.mul_re, Complex.mul_im]
  have hp (x : ℝ) : (0 : ℝ) ≤ ∑' k : ℤ, Real.exp (-s * ((k : ℝ) + x)^2) :=
    tsum_nonneg fun _ ↦ (Real.exp_pos _).le
  have he (x : ℝ) := Complex.tsum_exp_neg_quadratic (a := (t : ℂ)) ht (-(I * x))
  have hi (x : ℝ) : I * -(I * (x : ℂ)) = x := by rw [mul_neg, ← mul_assoc, I_mul_I]; simp
  simp_rw [hi, ← Complex.ofReal_intCast, ← Complex.ofReal_add, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_div, hdiv, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_tsum] at he
  have hz := he 0
  have ha := he a
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_intCast] at ha
  change (∑' k, term k) = _ at ha
  have bound := norm_tsum_le_tsum_norm (f := term)
    (by simpa only [hn] using gaussian_summable (mul_pos pi_pos ht))
  rw [ha, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp a)] at bound
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, add_zero] at hz
  simp only [← Complex.ofReal_exp, ← Complex.ofReal_tsum] at hz
  have eq := congrArg norm hz
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at eq
  rw [abs_of_nonneg (tsum_nonneg fun _ ↦ (Real.exp_pos _).le),
    abs_of_nonneg (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)] at eq
  simp only [hn, neg_mul] at bound
  simp only [neg_mul] at eq
  rw [eq] at bound
  simp only [neg_mul]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  exact le_of_mul_le_mul_left bound (norm_pos_iff.mpr (one_div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl htC))))

private theorem shifted_summable {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Summable fun k : ℤ ↦ Real.exp (-s * ((k : ℝ) + a)^2) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) _
    ((gaussian_summable (half_pos hs)).mul_left (Real.exp (s * a^2)))
  intro k
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hs.le (sq_nonneg ((k : ℝ) + 2*a))]

open InnerProductSpace

private theorem affineTheta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s g : ℝ} (hs : 0 < s) (hg : 0 < g) {n : ℕ} (b w : Fin n → E)
    (floor : ∀ i, g ≤ ‖w i‖) (diag : ∀ i, ⟪w i, b i⟫_ℝ = ‖w i‖^2)
    (orth : ∀ i j, i < j → ⟪w j, b i⟫_ℝ = 0) (v : E) :
    Summable (fun c : Fin n → ℤ ↦ Real.exp (-s * ‖v + ∑ i, (c i : ℝ) • b i‖^2)) ∧
    (∑' c : Fin n → ℤ, Real.exp (-s * ‖v + ∑ i, (c i : ℝ) • b i‖^2)) ≤
      (∑' k : ℤ, Real.exp (-(s*g^2) * (k : ℝ)^2))^n := by
  classical
  let T := ∑' k : ℤ, Real.exp (-(s*g^2) * (k : ℝ)^2)
  have hT : 0 ≤ T := tsum_nonneg fun _ ↦ (Real.exp_pos _).le
  induction n generalizing v with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp [Real.exp_le_one_iff]
      positivity
  | succ n ih =>
    let l := Fin.last n
    let u := w l
    have hu : 0 < ‖u‖ := hg.trans_le (floor l)
    let a := ⟪u, v⟫_ℝ / ‖u‖^2
    have hav : a * ‖u‖^2 = ⟪u, v⟫_ℝ := div_mul_cancel₀ _ (by positivity)
    let r (k : ℤ) := v + (k : ℝ) • b l - ((k : ℝ) + a) • u
    let P (c : Fin n → ℤ) := ∑ i, (c i : ℝ) • b i.castSucc
    let D (k : ℤ) := Real.exp (-(s * ‖u‖^2) * ((k : ℝ) + a)^2)
    let F (c : Fin (n+1) → ℤ) := Real.exp (-s * ‖v + ∑ i, (c i : ℝ) • b i‖^2)
    let e := Fin.snocEquiv (fun _ : Fin (n+1) ↦ ℤ)
    have split (k : ℤ) (c : Fin n → ℤ) :
        (F ∘ e) (k,c) = D k * Real.exp (-s * ‖r k + P c‖^2) := by
      have hp : ⟪u, P c⟫_ℝ = 0 := by
        simp [P, inner_sum, real_inner_smul_right, orth _ l (Fin.castSucc_lt_last _), u]
      have hr : ⟪u, r k⟫_ℝ = 0 := by
        simp only [r, inner_sub_right, inner_add_right, real_inner_smul_right,
          show ⟪u, b l⟫_ℝ = ‖u‖^2 from diag l, real_inner_self_eq_norm_sq]
        linarith only [hav]
      have heq : v + (P c + (k : ℝ) • b l) = ((k : ℝ) + a) • u + (r k + P c) := by
        dsimp [r]; abel
      simp only [Function.comp_apply, F, e, Fin.snocEquiv_apply, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last]
      change Real.exp (-s * ‖v + (P c + (k : ℝ) • b l)‖^2) = _
      dsimp only [D]
      rw [heq, norm_add_sq_real, real_inner_smul_left, inner_add_right, hr, hp, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, ← Real.exp_add]
      congr 1
      ring
    have pref (k : ℤ) := ih (fun i ↦ b i.castSucc) (fun i ↦ w i.castSucc)
      (fun i ↦ floor _) (fun i ↦ diag _) (fun i j h ↦ orth _ _ h) (r k)
    have row (k : ℤ) : Summable fun c ↦ (F ∘ e) (k,c) := by
      simpa only [split, P] using (pref k).1.mul_left (D k)
    have bound (k : ℤ) : (∑' c, (F ∘ e) (k,c)) ≤ D k * T^n := by
      simp_rw [split, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (pref k).2 (Real.exp_pos _).le
    have hd := shifted_summable (mul_pos hs (sq_pos_of_pos hu)) a
    have rows := Summable.of_nonneg_of_le (fun k ↦ tsum_nonneg
      (fun c ↦ (Real.exp_pos _).le)) bound (hd.mul_right (T^n))
    have total : Summable (F ∘ e) := (summable_prod_of_nonneg
      (fun _ ↦ (Real.exp_pos _).le)).2 ⟨row, rows⟩
    refine ⟨e.summable_iff.mp total, ?_⟩
    change (∑' c, F c) ≤ T^(n+1)
    rw [← e.tsum_eq F]
    change (∑' c, (F ∘ e) c) ≤ _
    rw [total.tsum_prod']
    · refine (rows.tsum_le_tsum bound (hd.mul_right _)).trans ?_
      rw [tsum_mul_right, pow_succ']
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hT _)
      apply (shiftedTheta_le (mul_pos hs (sq_pos_of_pos hu)) a).trans
      apply (gaussian_summable (mul_pos hs (sq_pos_of_pos hu))).tsum_le_tsum _
        (gaussian_summable (mul_pos hs (sq_pos_of_pos hg)))
      intro k
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left
        (sq_le_sq' (by linarith [floor l, norm_nonneg u]) (floor l)) hs.le)) (sq_nonneg _)
    · exact row

/-- The Gaussian mass of the integer span of a basis with Gram–Schmidt lengths at least
`g > 0` is bounded by the `n`th power of the one-dimensional Gaussian mass at scale `g`. -/
theorem latticeTheta_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) {s g : ℝ} (hs : 0 < s) (hg : 0 < g)
    (floor : ∀ i, g ≤ ‖gramSchmidt ℝ b i‖) :
    (∑' c : Fin n → ℤ, Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)) ≤
      (∑' k : ℤ, Real.exp (-(s*g^2) * (k : ℝ)^2))^n := by
  have diag (i) : ⟪gramSchmidt ℝ b i, b i⟫_ℝ = ‖gramSchmidt ℝ b i‖^2 := by
    conv_lhs => rhs; rw [gramSchmidt_def'' ℝ b i] -- expand only the input vector
    simp only [inner_add_right, real_inner_self_eq_norm_sq, inner_sum, real_inner_smul_right]
    rw [add_eq_left]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.mp hj).ne', mul_zero]
  simpa using (affineTheta hs hg b (gramSchmidt ℝ b) floor diag
    (fun _ _ h ↦ gramSchmidt_inv_triangular ℝ b h) 0).2

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.shiftedTheta_le

#print axioms SigabaNeo.Wall1.latticeTheta_le
