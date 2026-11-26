module

public import Definitions.Def_LatticeAttack_Reduction_BKZ

set_option autoImplicit true

public section

namespace SigabaNeo.LLL

open InnerProductSpace
open scoped RealInnerProductSpace

variable {n : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))

/-- Gram–Schmidt coefficient of row i in direction j. -/
noncomputable def mu (i j : Fin n) : ℝ :=
  ⟪gramSchmidt ℝ b j, b i⟫_ℝ / ‖gramSchmidt ℝ b j‖ ^ 2

/-- Size reduction and the Lovász inequality with δ = 3/4. -/
structure LLLReduced : Prop where
  size_reduced : ∀ i j, j < i → |mu b i j| ≤ 1 / 2
  lovasz : ∀ i j : Fin n, j.val = i.val + 1 →
    (3 / 4 - mu b j i ^ 2) * ‖gramSchmidt ℝ b i‖ ^ 2 ≤ ‖gramSchmidt ℝ b j‖ ^ 2

theorem last_column_bound (hb : LinearIndependent ℝ b) (z : Fin n → ℤ) (k : Fin n)
    (hk : z k ≠ 0) (htop : ∀ j > k, z j = 0) :
    ‖gramSchmidt ℝ b k‖ ≤ ‖∑ j, z j • b j‖ := by
  let g := gramSchmidt ℝ b k
  have e : ⟪g, ∑ j, z j • b j⟫_ℝ = (z k : ℝ) * ‖g‖ ^ 2 := by
    simp only [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
    rw [Finset.sum_eq_single k]
    · rw [show ⟪g, b k⟫_ℝ = ‖g‖ ^ 2 from BKZ.inner_diag b k]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · simp [g, gramSchmidt_inv_triangular ℝ b h]
      · simp [htop j h]
    · simp
  have cs := abs_real_inner_le_norm g (∑ j, z j • b j)
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg ‖g‖)] at cs
  have hz : (1 : ℝ) ≤ |(z k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hp : 0 < ‖g‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero k hb)
  apply le_of_mul_le_mul_left (a := ‖g‖) _ hp
  nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg ‖g‖)]

variable [NeZero n]

private theorem first_le_column (hr : LLLReduced b) (k : Fin n) :
    ‖b 0‖ ^ 2 ≤ (2 : ℝ) ^ k.val * ‖gramSchmidt ℝ b k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero =>
    have he : Finset.Iio (⟨0,hk⟩ : Fin n) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦
        Nat.not_lt_zero j.val (show j < (⟨0,hk⟩ : Fin n) from Finset.mem_Iio.mp hj)
    rw [gramSchmidt_def, he]
    simp
  | succ k ih =>
    let i : Fin n := ⟨k, by omega⟩
    let j : Fin n := ⟨k+1, hk⟩
    have s := hr.size_reduced j i (show i < j from Nat.lt_succ_self k)
    have m : mu b j i ^ 2 ≤ (1/2 : ℝ)^2 := by
      simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)).mpr s
    have l := hr.lovasz i j rfl
    have step : ‖gramSchmidt ℝ b i‖ ^ 2 ≤ 2 * ‖gramSchmidt ℝ b j‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right m (sq_nonneg ‖gramSchmidt ℝ b i‖)]
    apply (ih i.isLt).trans
    change (2:ℝ)^k * _ ≤ 2^(k+1) * ‖gramSchmidt ℝ b j‖^2
    rw [pow_succ (2 : ℝ) k, mul_assoc]
    exact mul_le_mul_of_nonneg_left step (by positivity)

theorem reduced_approx_factor (hb : LinearIndependent ℝ b) (hr : LLLReduced b)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Submodule.span ℤ (Set.range b)) (hne : v ≠ 0) :
    ‖b 0‖ ≤ (2 : ℝ) ^ (((n : ℝ) - 1) / 2) * ‖v‖ := by
  classical
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  let s := Finset.univ.filter fun j ↦ z j ≠ 0
  have hs : s.Nonempty := by
    by_contra! empty
    apply hne
    rw [← hz]
    apply Finset.sum_eq_zero
    intro j _
    have : z j = 0 := by
      by_contra nz
      have mem : j ∈ s := by simp [s,nz]
      simp [empty] at mem
    simp [this]
  let k := s.max' hs
  have mem : k ∈ s := s.max'_mem hs
  have h := last_column_bound b hb z k (Finset.mem_filter.mp mem).2 (by
    intro j gt
    by_contra nz
    exact gt.not_ge (s.le_max' j (by simp [s,nz])))
  rw [hz] at h
  have hkn : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
  have p : (2 : ℝ)^k.val ≤ (2 : ℝ)^((n : ℝ)-1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ)^_), ← Real.rpow_mul (by norm_num)]
  push_cast
  rw [show ((n : ℝ)-1)/2*2 = n-1 by ring]
  exact (first_le_column b hr k).trans (mul_le_mul p
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h) (sq_nonneg _) (by positivity))

theorem unique_shortest_of_approx {γ : ℝ}
    (approx : ∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ‖b 0‖ ≤ γ * ‖v‖)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} → γ * ‖u‖ < ‖w‖) :
    b 0 ∈ Submodule.span ℤ {u} := by
  by_contra h
  exact (gap _ (Submodule.subset_span (Set.mem_range_self 0)) h).not_ge (approx u hu hne)

theorem reduced_unique_shortest (hb : LinearIndependent ℝ b) (hr : LLLReduced b)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} →
      (2 : ℝ) ^ (((n : ℝ) - 1) / 2) * ‖u‖ < ‖w‖) :
    b 0 ∈ Submodule.span ℤ {u} :=
  unique_shortest_of_approx b (reduced_approx_factor b hb hr) hu hne gap

theorem bkz_unique_shortest (hb : LinearIndependent ℝ b) {β : ℕ} (hr : BKZ.Reduced b hb β)
    (hβ : 2 ≤ β) (hn : β ≤ n) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} →
      (((β : ℝ)+4)/Real.pi) ^ (((n : ℝ)-1)/((β : ℝ)-1)) * ‖u‖ < ‖w‖) :
    b 0 ∈ Submodule.span ℤ {u} :=
  unique_shortest_of_approx b (BKZ.reduced_approx_factor b hb hr hβ hn) hu hne gap

theorem nonzero_multiple_of_mem (hb : LinearIndependent ℝ b) {u : EuclideanSpace ℝ (Fin n)}
    (h : b 0 ∈ Submodule.span ℤ {u}) : ∃ k : ℤ, k ≠ 0 ∧ b 0 = k • u := by
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h
  refine ⟨k, ?_, hk.symm⟩
  rintro rfl
  exact hb.ne_zero 0 (by simpa using hk.symm)

end SigabaNeo.LLL
