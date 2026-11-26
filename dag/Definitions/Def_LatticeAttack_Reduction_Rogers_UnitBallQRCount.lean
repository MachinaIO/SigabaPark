import Definitions.Def_LatticeAttack_Reduction_Rogers_UnitBallCoverIntegral
import Definitions.Def_LatticeAttack_Reduction_Rogers_GramParameterProofs

set_option autoImplicit true

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ENNReal NNReal
namespace SigabaNeo.Rogers

private abbrev Site {n : ℕ} (g : SL n) := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
private def hits {n : ℕ} (g : SL n) (j : ℕ) : Set (Site g) := {x | x.val ∈ densityBall n j}

private theorem work_eq {n : ℕ} (g : SL n) (j : ℕ) :
    densityWork n j g = (ENat.card (hits g j) : ℝ≥0∞) * (volume (densityBall n j))⁻¹ := by
  classical
  unfold densityWork tupleWorkload
  trans ∑' x : Site g, densityTest n j x.val
  · exact (Equiv.funUnique (Fin 1) (Site g)).tsum_eq (fun x ↦ densityTest n j x.val)
  change (∑' x, (hits g j).indicator (fun _ ↦ (volume (densityBall n j))⁻¹) x) = _
  rw [← tsum_subtype, ENNReal.tsum_const]


theorem unit_ball_work_le_qr_product (d : ℕ) (hd : 1 ≤ d) (g : SL (d+1)) :
    densityWork (d+1) 0 g ≤ unitBallQRBound d g := by
  classical
  obtain ⟨k,u,a,hk,ha,hu,hz,hg,ht,hv⟩ := gramParamsRealized d hd g
  have hU : u.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := u) (fun {_ _} h ↦ hz _ _ h)]
    simp [hu]
  have hkdet := congrArg Matrix.det hk
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hkdet
  have hdet := congrArg Matrix.det hg
  simp only [g.property, Matrix.det_mul, Matrix.det_diagonal, hU, mul_one] at hdet
  have hp := Finset.prod_pos (s := Finset.univ) (fun i _ ↦ ha i)
  have hkpos : 0 < k.det := by by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hp.le]
  have hk1 : k.det = 1 := by nlinarith
  have hprod : ∏ i, a i = 1 := by simpa [hk1] using hdet.symm
  let t (i : Fin d) := Real.log (a i.succ) - Real.log (a i.castSucc)
  have diff (i : Fin (d+1)) : columnDiagLogs t i - Real.log (a i) =
      columnDiagLogs t 0 - Real.log (a 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      have h := columnDiagLogs_diff t j
      dsimp only [t] at h
      linarith
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ diff i)
  rw [Finset.sum_sub_distrib, columnDiagLogs_sum, ← Real.log_prod (fun i _ ↦ (ha i).ne'),
    hprod, Real.log_one, sub_zero] at hsum
  have hc : columnDiagLogs t 0 - Real.log (a 0) = 0 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left (by positivity)
  have he (i) : Real.exp (columnDiagLogs t i) = a i := by
    rw [sub_eq_zero.mp ((diff i).trans hc), Real.exp_log (ha i)]
  let e (i : Fin (d+1)) : E (d+1) := WithLp.toLp 2 (k.col i)
  have orth : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simpa [e, Matrix.col, Matrix.mul_apply, Matrix.one_apply, PiLp.inner_apply,
      real_inner_eq_re_inner, mul_comm] using congrArg (fun m : Matrix _ _ ℝ ↦ m i j) hk
  have expand (j : Fin (d+1)) : qrColumn g j = ∑ i, (a i * u i j) • e i := by
    ext t
    simp [qrColumn, hg, Matrix.mul_apply, Matrix.diagonal_apply, e, Matrix.col,
      mul_comm, mul_left_comm]
  have coeff (i j : Fin (d+1)) : inner ℝ (e i) (qrColumn g j) = a i * u i j := by
    rw [expand, inner_sum]
    simp [real_inner_smul_right, orthonormal_iff_ite.mp orth]
  let T := g.toLin'.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (d+1)) ℝ).symm
  have ex (x : hits g 0) : ∃ z : Fin (d+1) → ℤ, T (fun i ↦ (z i : ℝ)) = x.val.val :=
    by have hx := x.val.property.1; exact (points_mk g ▸ hx : x.val.val ∈ Set.range (fun z : Fin (d+1) → ℤ ↦ T (fun i ↦ (z i : ℝ))))
  let z (x : hits g 0) := (ex x).choose
  have repr (x : hits g 0) : x.val.val = ∑ j, (z x j : ℝ) • qrColumn g j := by
    rw [← (ex x).choose_spec]
    ext i
    change (∑ j, g.val i j * _) = _
    simp [qrColumn, mul_comm, z]
  let m i := ⌊2 / a i⌋₊ + 1
  let (i : Fin (d+1)) : NeZero (m i) := ⟨Nat.succ_ne_zero _⟩
  let code (x : hits g 0) (i : Fin (d+1)) : ZMod (m i) := (z x i : ZMod (m i))
  have inj : Function.Injective code := by
    intro x y hxy
    have same (i) : z x i = z y i := by
      induction i using (inferInstance : WellFoundedGT (Fin (d+1))).induction with
      | ind i ih =>
        have proj : inner ℝ (e i) (x.val.val - y.val.val) =
            ((z x i : ℝ) - z y i) * a i := by
          rw [inner_sub_right, repr x, repr y, inner_sum, inner_sum, ← Finset.sum_sub_distrib,
            Finset.sum_eq_single i]
          · simp [real_inner_smul_right, coeff, hu, sub_mul]
          · intro j _ hj
            rcases lt_or_gt_of_ne hj with h | h
            · simp [real_inner_smul_right, coeff, hz _ _ h]
            · simp [ih j h]
          · simp
        have small (w : hits g 0) : ‖w.val.val‖ < 1 := by
          simpa [hits,densityBall] using w.property
        have bound := abs_real_inner_le_norm (e i) (x.val.val - y.val.val)
        rw [proj, abs_mul, abs_of_pos (ha i), orth.1 i, one_mul] at bound
        have lt : |(z x i : ℝ) - z y i| < 2 / a i := (lt_div_iff₀ (ha i)).mpr (bound.trans_lt
          ((norm_sub_le _ _).trans_lt (by linarith [small x, small y])))
        have dvd : (m i : ℤ) ∣ z x i - z y i := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
          rw [Int.cast_sub, sub_eq_zero]
          exact congrFun hxy i
        apply Int.eq_of_sub_eq_zero
        apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs dvd
        have hh := lt.trans (Nat.lt_floor_add_one (2 / a i))
        simpa [m, ← Nat.cast_lt (α := ℝ), Nat.cast_natAbs, Int.cast_sub, abs_of_nonneg (by positivity : 0 ≤ (⌊2 / a i⌋₊ : ℝ) + 1)] using hh
    exact Subtype.ext (Subtype.ext (by simp only [repr x, repr y, same]))
  have card := ENat.toENNReal_mono (ENat.card_le_card_of_injective inj)
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_pi] at card
  simp only [ZMod.card, ENat.toENNReal_coe] at card
  rw [work_eq, unitBallQRBound, mul_comm]
  apply mul_le_mul_right (card.trans ?_) _
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
  intro i _
  rw [← ht, Real.exp_neg, he]
  simpa [m, div_eq_mul_inv, add_comm] using
    add_le_add_right (Nat.floor_le (div_nonneg (by norm_num) (ha i).le : 0 ≤ 2 / a i)) 1

#print axioms unit_ball_work_le_qr_product
end SigabaNeo.Rogers
