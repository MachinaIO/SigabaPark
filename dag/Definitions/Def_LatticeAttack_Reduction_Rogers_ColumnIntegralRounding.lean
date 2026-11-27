module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnCandidateAssembly
public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnPositiveQR

set_option autoImplicit true

@[expose] public section
noncomputable section
namespace SigabaNeo.Rogers

private def coeff {n : ℕ} (r : Matrix (Fin n) (Fin n) ℝ) (j i : Fin n) : ℤ :=
  if i < j then -round ((∑ t : {t : Fin n // i < t},
    r i t * (coeff r j t : ℝ)) / r i i)
  else if i = j then 1 else 0
termination_by n - i.val
decreasing_by have := t.property; omega

theorem columnIntegralRounding {n : ℕ} (r : Matrix (Fin n) (Fin n) ℝ)
    (hp : ∀ i, 0 < r i i) (ht : ∀ i j, j < i → r i j = 0) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
      let s := r * (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val
      (∀ i, s i i = r i i) ∧ (∀ i j, j < i → s i j = 0) ∧
      (∀ i j, i < j → |s i j| ≤ s i i / 2) := by
  classical
  let u : Matrix (Fin n) (Fin n) ℤ := fun i j ↦ coeff r j i
  have ud (i) : u i i = 1 := by rw [show u i i = coeff r i i from rfl, coeff]; simp
  have ut (i j) (h : j < i) : u i j = 0 := by
    change coeff r j i = _
    rw [coeff]; simp [h.not_gt, h.ne']
  let γ : Matrix.SpecialLinearGroup (Fin n) ℤ :=
    ⟨u, by rw [Matrix.det_of_isUpperTriangular ut]; simp [ud]⟩
  refine ⟨γ, ?_⟩
  let s := r * (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val
  let tail (i j : Fin n) := ∑ t : {t : Fin n // i < t}, r i t * (u t j : ℝ)
  have split (i j) : s i j = r i i * (u i j : ℝ) + tail i j := by
    change (∑ t, r i t * (u t j : ℝ)) = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    unfold tail
    rw [← Finset.sum_subtype (Finset.Ioi i) (fun t ↦ Finset.mem_Ioi) (fun t ↦ r i t * (u t j : ℝ))]
    symm
    apply Finset.sum_subset
    · intro t h
      exact Finset.mem_erase.mpr ⟨(Finset.mem_Ioi.mp h).ne', Finset.mem_univ _⟩
    · intro t ht' hnot
      have hlt : t < i := lt_of_le_of_ne (le_of_not_gt (fun h ↦ hnot (Finset.mem_Ioi.mpr h)))
        (Finset.mem_erase.mp ht').1
      simp [ht i t hlt]
  have tz (i j) (h : j ≤ i) : tail i j = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    simp [ut _ _ (h.trans_lt t.property)]
  have sd (i) : s i i = r i i := by simp [split, ud, tz]
  refine ⟨sd, fun i j h ↦ ?_, fun i j h ↦ ?_⟩
  · change s i j = 0
    simp [split, ut _ _ h, tz _ _ h.le]
  · change |s i j| ≤ s i i / 2
    rw [sd, split]
    have hu : u i j = -round (tail i j / r i i) := by
      change coeff r j i = _
      rw [coeff, ite_eq_left h]
    rw [hu, Int.cast_neg]
    have he : r i i * -(round (tail i j / r i i) : ℝ) + tail i j =
        (tail i j / r i i - round (tail i j / r i i)) * r i i := by
      field_simp [(hp i).ne']; ring
    rw [he, abs_mul, abs_of_pos (hp i)]
    linarith [mul_le_mul_of_nonneg_right (abs_sub_round (tail i j / r i i)) (hp i).le]

theorem columnCandidate_nonempty {n : ℕ} (x : SL n) : Nonempty (ColumnCandidate x) := by
  obtain ⟨k, r, hk, hx, hp, ht⟩ := columnPositiveQR x
  obtain ⟨γ, he, hu, hr⟩ := columnIntegralRounding r hp ht
  exact columnCandidate_of_qr_and_multiplier x k r hk hx γ _ rfl
    (fun i ↦ (he i).symm ▸ hp i) hu hr

#print axioms columnCandidate_nonempty

end SigabaNeo.Rogers
