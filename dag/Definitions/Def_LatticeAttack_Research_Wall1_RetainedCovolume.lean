module

public import Definitions.Def_LatticeAttack_Research_Wall1_MinkowskiBound
public import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedLength

set_option autoImplicit true

public section

open MeasureTheory Metric Module

namespace SigabaNeo.Wall1

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- Minkowski's elementary first-minimum constant in dimension n. -/
noncomputable def minkowskiConstant (n : ℕ) : ℝ :=
  2 / volume.real (ball (0 : E n) 1) ^ (1 / (n : ℝ))

private theorem unitVolume_pos (n : ℕ) : 0 < volume.real (ball (0 : E n) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- A nonzero minimizer in the integer span of the window basis. -/
def IsWindowShortest {n : ℕ} (B : Basis (Fin n) ℝ (E n)) (v : E n) : Prop :=
  v ∈ Submodule.span ℤ (Set.range B) ∧ v ≠ 0 ∧
    ∀ w ∈ Submodule.span ℤ (Set.range B), w ≠ 0 → ‖v‖ ≤ ‖w‖

theorem shortest_norm_le_minkowski {n : ℕ} [NeZero n] (B : Basis (Fin n) ℝ (E n))
    {v : E n} (hv : IsWindowShortest B v) :
    ‖v‖ ≤ minkowskiConstant n * ZLattice.covolume (Submodule.span ℤ (Set.range B)) ^
      (1 / (n : ℝ)) := by
  obtain ⟨w, hw, hw₀, h⟩ := minkowski_short_vector_det B
  apply (hv.2.2 w hw hw₀).trans
  have h' := Real.rpow_le_rpow (pow_nonneg (norm_nonneg w) n)
    ((le_div_iff₀ (unitVolume_pos n)).2 h) (inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (NeZero.ne n),
    Real.div_rpow (by positivity) (unitVolume_pos n).le,
    Real.mul_rpow (by positivity) (abs_nonneg _),
    Real.pow_rpow_inv_natCast (by norm_num) (NeZero.ne n)] at h'
  rw [minkowskiConstant, minkowski_covolume_eq_abs_det, one_div]
  exact h'.trans_eq (by ring)

/-- Intrinsic covolumes in basis coordinates. The primitive head is part of the given
basis, and the projected tail generates the image lattice in its span. -/
theorem projected_tail_covolume {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (B : Basis (Fin (n + 1)) ℝ F) :
    Real.sqrt (Matrix.gram ℝ (fun i : Fin n ↦ (ℝ ∙ B 0)ᗮ.starProjection (B i.succ))).det =
      Real.sqrt (Matrix.gram ℝ B).det / ‖B 0‖ := by
  apply (eq_div_iff (norm_ne_zero_iff.mpr (B.ne_zero 0))).2
  rw [det_gram_project_tail, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]

/-- The reducer supplies the input covolume of each window and the retained-volume update. -/
theorem retained_log_covolume_lower_bound {n : ℕ} [NeZero n] (T : ℕ) (D : ℕ → ℝ)
    (B : ℕ → Basis (Fin n) ℝ (E n)) (v : ℕ → E n) (hD : 0 < D 0)
    (hwindow : ∀ t < T, ZLattice.covolume (Submodule.span ℤ (Set.range (B t))) = D t)
    (hshort : ∀ t < T, IsWindowShortest (B t) (v t))
    (hstep : ∀ t < T, D (t + 1) = D t / ‖v t‖) :
    (((n : ℝ) - 1) / n) ^ T * Real.log (D 0) -
      Real.log (minkowskiConstant n) * ∑ i ∈ Finset.range T, (((n : ℝ) - 1) / n) ^ i ≤
        Real.log (D T) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  apply log_volume_lower_bound D (fun k ↦ ‖v (k - 1)‖) n (minkowskiConstant n) T (by exact_mod_cast hn)
    (div_pos (by norm_num) (Real.rpow_pos_of_pos (unitVolume_pos n) _)) hD
  · simpa using hstep
  · intro t ht
    simpa [hwindow t ht] using
      And.intro (norm_pos_iff.mpr (hshort t ht).2.1) (shortest_norm_le_minkowski _ (hshort t ht))

#print axioms shortest_norm_le_minkowski
#print axioms projected_tail_covolume
#print axioms retained_log_covolume_lower_bound

end SigabaNeo.Wall1
