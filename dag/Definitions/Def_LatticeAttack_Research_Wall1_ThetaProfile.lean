module

public import Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta
import all Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

open InnerProductSpace

/-- Centered one-dimensional integer Gaussian mass at inverse squared scale `a`. -/
noncomputable def thetaFactor (a : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-a * (k : ℝ)^2)

private theorem affineThetaProfile {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : ℝ} (hs : 0 < s) {n : ℕ} (b w : Fin n → E)
    (pos : ∀ i, 0 < ‖w i‖) (diag : ∀ i, ⟪w i, b i⟫_ℝ = ‖w i‖^2)
    (orth : ∀ i j, i < j → ⟪w j, b i⟫_ℝ = 0) (v : E) :
    Summable (fun c : Fin n → ℤ ↦ Real.exp (-s * ‖v + ∑ i, (c i : ℝ) • b i‖^2)) ∧
    (∑' c : Fin n → ℤ, Real.exp (-s * ‖v + ∑ i, (c i : ℝ) • b i‖^2)) ≤
      ∏ i, thetaFactor (s * ‖w i‖^2) := by
  classical
  induction n generalizing v with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp [Real.exp_le_one_iff]
      positivity
  | succ n ih =>
    let l := Fin.last n
    let u := w l
    have hu : 0 < ‖u‖ := pos l
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
      (fun i ↦ pos _) (fun i ↦ diag _) (fun i j h ↦ orth _ _ h) (r k)
    have row (k : ℤ) : Summable fun c ↦ (F ∘ e) (k,c) := by
      simpa only [split, P] using (pref k).1.mul_left (D k)
    let Pθ := ∏ i : Fin n, thetaFactor (s * ‖w i.castSucc‖^2)
    have bound (k : ℤ) : (∑' c, (F ∘ e) (k,c)) ≤ D k * Pθ := by
      simp_rw [split, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (pref k).2 (Real.exp_pos _).le
    have hd := shifted_summable (mul_pos hs (sq_pos_of_pos hu)) a
    have rows := Summable.of_nonneg_of_le (fun k ↦ tsum_nonneg
      (fun c ↦ (Real.exp_pos _).le)) bound (hd.mul_right (Pθ))
    have total : Summable (F ∘ e) := (summable_prod_of_nonneg
      (fun _ ↦ (Real.exp_pos _).le)).2 ⟨row, rows⟩
    refine ⟨e.summable_iff.mp total, ?_⟩
    change (∑' c, F c) ≤ ∏ i, thetaFactor (s * ‖w i‖^2)
    rw [← e.tsum_eq F]
    change (∑' c, (F ∘ e) c) ≤ _
    rw [total.tsum_prod']
    · refine (rows.tsum_le_tsum bound (hd.mul_right _)).trans ?_
      rw [tsum_mul_right, Fin.prod_univ_castSucc, mul_comm]
      exact mul_le_mul_of_nonneg_left (shiftedTheta_le (mul_pos hs (sq_pos_of_pos hu)) a)
        (Finset.prod_nonneg fun _ _ ↦ tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
    · exact row

/-- Gaussian mass bounded by the product at the actual Gram–Schmidt lengths. -/
theorem latticeThetaProfile {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) {s : ℝ} (hs : 0 < s) :
    Summable (fun c : Fin n → ℤ ↦ Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)) ∧
    (∑' c : Fin n → ℤ, Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)) ≤
      ∏ i, thetaFactor (s * ‖gramSchmidt ℝ b i‖^2) := by
  have diag (i) : ⟪gramSchmidt ℝ b i, b i⟫_ℝ = ‖gramSchmidt ℝ b i‖^2 := by
    conv_lhs => rhs; rw [gramSchmidt_def'' ℝ b i] -- expand only the input vector
    simp only [inner_add_right, real_inner_self_eq_norm_sq, inner_sum, real_inner_smul_right]
    rw [add_eq_left]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.mp hj).ne', mul_zero]
  simpa using (affineThetaProfile hs b (gramSchmidt ℝ b)
    (fun i ↦ norm_pos_iff.mpr (gramSchmidt_ne_zero i b.linearIndependent)) diag
    (fun _ _ h ↦ gramSchmidt_inv_triangular ℝ b h) 0)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.latticeThetaProfile
