module

public import Definitions.Def_LatticeAttack_Research_Wall1_GramFactor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Take the head, project the remaining vectors perpendicular to it, and repeat. -/
noncomputable def successiveProjections : {n : ℕ} → (Fin n → E) → Fin n → E
  | 0, _ => Fin.elim0
  | n + 1, b => Fin.cons (α := fun _ ↦ E) (b 0) (successiveProjections
      (fun i : Fin n ↦ (ℝ ∙ b 0)ᗮ.starProjection (b i.succ)))

/-- The Gram determinant is the product of squared successive projection lengths. -/
theorem det_gram_eq_prod_norm_sq {n : ℕ} (b : Fin n → E) :
    (Matrix.gram ℝ b).det = ∏ i, ‖successiveProjections b i‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_gram_project_tail, ih, Fin.prod_univ_succ]
    simp [successiveProjections]

/-- A cap on each divisor gives a geometric lower bound on the terminal log volume. -/
theorem log_volume_lower_bound (D s : ℕ → ℝ) (b C : ℝ) (T : ℕ)
    (hb : 1 ≤ b) (hC : 0 < C) (hD : 0 < D 0)
    (hstep : ∀ t < T, D (t + 1) = D t / s (t + 1))
    (hcap : ∀ t < T, 0 < s (t + 1) ∧ s (t + 1) ≤ C * D t ^ (1 / b)) :
    ((b - 1) / b) ^ T * Real.log (D 0) -
      Real.log C * ∑ i ∈ Finset.range T, ((b - 1) / b) ^ i ≤ Real.log (D T) := by
  let r := (b - 1) / b
  have hb' : 0 < b := by linarith
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hb) hb'.le
  have hr' : r = 1 - 1 / b := by dsimp [r]; field_simp
  have aux (t : ℕ) (ht : t ≤ T) : 0 < D t ∧
      r ^ t * Real.log (D 0) - Real.log C * ∑ i ∈ Finset.range t, r ^ i ≤
        Real.log (D t) := by
    induction t with
    | zero => simpa using hD
    | succ t ih =>
      obtain ⟨hd, hprev⟩ := ih (by omega)
      obtain ⟨hs, hle⟩ := hcap t (by omega)
      rw [hstep t (by omega)]
      refine ⟨div_pos hd hs, ?_⟩
      have hlog := Real.log_le_log hs hle
      rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd _).ne', Real.log_rpow hd] at hlog
      rw [Real.log_div hd.ne' hs.ne', Finset.sum_range_succ', pow_succ,
        show (∑ k ∈ Finset.range t, r ^ (k + 1)) = r * ∑ k ∈ Finset.range t, r ^ k by
          simp [Finset.mul_sum, pow_succ']]
      simp only [pow_zero]
      have hsingle : r * Real.log (D t) - Real.log C ≤ Real.log (D t) - Real.log (s (t + 1)) := by
        rw [hr']; linarith
      exact le_trans (by nlinarith [mul_le_mul_of_nonneg_left hprev hr]) hsingle
  exact (aux T le_rfl).2

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.det_gram_eq_prod_norm_sq
#print axioms SigabaNeo.Wall1.log_volume_lower_bound
