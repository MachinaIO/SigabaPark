import Definitions.Def_LatticeAttack_Reduction_Rogers_UnitBallCoverIntegral
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelCandidate
import Definitions.Def_LatticeAttack_Reduction_Rogers_GramParameterProofs

set_option autoImplicit true

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SigabaNeo.Rogers

def qrProduct {d : ℕ} (t : Fin d → ℝ) : ℝ :=
  ∏ i, (1 + 2 * Real.exp (-columnDiagLogs t i))

private theorem measurable_qrProduct (d : ℕ) : Measurable (@qrProduct d) := by
  have h (i : Fin (d+1)) : Measurable (fun t : Fin d → ℝ ↦ Fin.partialSum t i) := by
    induction i using Fin.induction with
    | zero => simp
    | succ k ih => simp only [Fin.partialSum_succ]; exact ih.add (measurable_pi_apply k)
  unfold qrProduct columnDiagLogs
  fun_prop

abbrev qrWeight {d : ℕ} (i : Fin d) : ℝ := (i.val + 1 : ℕ) * ((d-i.val : ℕ) : ℝ)

theorem unitBallQRIntegral_of_decay (d : ℕ) (hd : 1 ≤ d)
    (decay : ∃ (A : ℝ) (w : Fin d → ℝ), (∀ i, 0 < w i) ∧
      ∀ t : Fin d → ℝ, (∀ i, -Real.log 2 / 2 ≤ t i) →
        (∏ i, Real.exp (-qrWeight i * t i)) * qrProduct t ≤
          A * ∏ i, Real.exp (-w i * t i)) :
    (∫⁻ g in columnSiegelSet (d+1), unitBallQRBound d g ∂groupHaar (d+1)) ≠ ⊤ := by
  obtain ⟨A,w,hw,hA⟩ := decay
  let b := -Real.log 2 / 2
  let S : Set (Fin d → ℝ) := univ.pi fun _ ↦ Ici b
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici
  have hq : Measurable (fun t : Fin d → ℝ ↦ ENNReal.ofReal (qrProduct t)) := ENNReal.measurable_ofReal.comp (measurable_qrProduct d)
  have root : (∫⁻ t in S, ENNReal.ofReal (qrProduct t) ∂columnRootMeasure d) ≠ ⊤ := by
    rw [columnRootMeasure, setLIntegral_withDensity_eq_lintegral_mul₀ (f := fun t : Fin d → ℝ ↦ ENNReal.ofReal (∏ i, Real.exp (-qrWeight i * t i))) (Measurable.aemeasurable (by fun_prop)) hq.aemeasurable hS]
    refine ne_top_of_le_ne_top (b := ∫⁻ t in S, ENNReal.ofReal A *
      ENNReal.ofReal (∏ i, Real.exp (-w i * t i)) ∂Measure.pi (fun _ ↦ volume)) ?_
      (setLIntegral_mono' hS (fun t ht ↦ ?_))
    case refine_2 =>
      change ENNReal.ofReal _ * ENNReal.ofReal _ ≤ _
      rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ ↦ (Real.exp_pos _).le)]
      exact (ENNReal.ofReal_le_ofReal (hA t fun i ↦ ht i trivial)).trans
        (by rw [mul_comm A, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ ↦ (Real.exp_pos _).le), mul_comm])
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    dsimp only [S]
    rw [Measure.restrict_pi_pi]
    simp_rw [← restrict_Ioi_eq_restrict_Ici]
    rw [siegel_diagonal_integral w hw]
    exact ENNReal.ofReal_ne_top
  have chart : IsColumnChart (@gramColumnParameters d) :=
    ⟨measurable_gramColumnParameters d, fun g p ↦ ⟨gramParamsRecovered d hd g p,
      fun e ↦ e ▸ gramParamsRealized d hd g⟩⟩
  let : SigmaFinite (columnRootMeasure d) := by unfold columnRootMeasure; infer_instance
  obtain ⟨C,hC⟩ := columnQRHaarPushforward hd chart
  let F (p : ColumnParameters d) := ENNReal.ofReal (qrProduct p.1)
  have hF : Measurable F := hq.comp measurable_fst
  apply ne_top_of_le_ne_top _ (lintegral_mono_set (columnSiegel_subset_rectangle d))
  unfold unitBallQRBound
  have hv : volume (densityBall (d+1) 0) ≠ 0 := by
    simpa [densityBall] using (Metric.measure_ball_pos (volume : Measure (E (d+1))) 0 one_pos).ne'
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hv), columnRectangle_preimage chart]
  apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hv)
  change (∫⁻ g in gramColumnParameters ⁻¹' (S ×ˢ upperCube _), F (gramColumnParameters g)
    ∂groupHaar _) ≠ ⊤
  rw [← setLIntegral_map (hS.prod (show MeasurableSet (upperCube (d+1)) from measurableSet_Icc)) hF chart.1, hC, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  rw [← Measure.prod_restrict, lintegral_prod F hF.aemeasurable]
  simpa [F, lintegral_const, upperCube_volume] using root

end SigabaNeo.Rogers

namespace SigabaNeo.Rogers

private theorem qrDecay (d : ℕ) (hd : 1 ≤ d) :
    ∃ (A : ℝ) (w : Fin d → ℝ), (∀ i, 0 < w i) ∧
      ∀ t : Fin d → ℝ, (∀ i, -Real.log 2 / 2 ≤ t i) →
        (∏ i, Real.exp (-qrWeight i * t i)) * qrProduct t ≤
          A * ∏ i, Real.exp (-w i * t i) := by
  classical
  let n : ℝ := d+1
  have hn : 1 < n := by dsimp [n]; exact_mod_cast (by omega : 1 < d+1)
  have hn0 : 0 < n := by linarith
  let L := Real.log 2 / 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let B := n * L
  let w (i : Fin d) := qrWeight i * (1 - 1/n)
  refine ⟨(3 * Real.exp B)^(d+1) * Real.exp ((∑ i : Fin d, qrWeight i * L)/n), w, ?_, ?_⟩
  · intro i
    have : 0 < d-i.val := Nat.sub_pos_of_lt i.isLt
    exact mul_pos (by unfold qrWeight; positivity) (sub_pos.mpr ((div_lt_iff₀ hn0).mpr (by linarith)))
  intro t ht
  let x := columnDiagLogs t
  let y (i : Fin (d+1)) := x i + i.val * L
  have hy : Monotone y := Fin.monotone_iff_le_succ.mpr fun i ↦ by
    have h := columnDiagLogs_diff t i
    have ht' : -L ≤ t i := by dsimp [L]; linarith [ht i]
    simp only [y, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    dsimp [x]; linarith [show ((i.val : ℝ)+1)*L = i.val*L+L by ring]
  let D (i j : Fin (d+1)) := if i < j then y j-y i else 0
  have posD (i j) : 0 ≤ D i j := by unfold D; split <;> first | exact sub_nonneg.mpr (hy (by omega)) | rfl
  have diff (i j) : x j - x i ≤ D i j + B := by
    have hi : (i.val : ℝ) ≤ n := by dsimp [n]; exact_mod_cast i.isLt.le
    have hj : 0 ≤ (j.val : ℝ) * L := by positivity
    have h : y j - y i ≤ D i j := by
      unfold D; split
      · rfl
      · exact sub_nonpos.mpr (hy (by omega))
    dsimp [y,B] at *; linarith [mul_le_mul_of_nonneg_right hi hL]
  have row (i) : -x i ≤ (∑ j, D i j)/n + B := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ diff i j
    simp [Finset.sum_sub_distrib,Finset.sum_add_distrib,x,columnDiagLogs_sum,nsmul_eq_mul] at h
    rw [← sub_le_iff_le_add, le_div_iff₀ hn0]
    dsimp [n,x]; nlinarith
  have sumD : (∑ i, ∑ j, D i j) = ∑ i, qrWeight i * (t i + L) := by
    have he : ∀ i : Fin d, y i.succ - y i.castSucc = t i + L := by
      intro i
      simp only [y, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      dsimp [x]; linarith [columnDiagLogs_diff t i, show ((i.val : ℝ)+1)*L = i.val*L+L by ring]
    rw [← show (∑ i, qrWeight i * (y i.succ - y i.castSucc)) = ∑ i, qrWeight i * (t i + L) by simp_rw [he],
      ← sum_column_log_ratios]
    unfold D
    rw [← Fintype.sum_prod_type']
    symm
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun p : Fin (d+1) × Fin (d+1) ↦ p.1 < p.2)) (by simp) (fun p ↦ y p.2 - y p.1)).symm
  have factor (i) : 1 + 2 * Real.exp (-x i) ≤
      (3 * Real.exp B) * Real.exp ((∑ j, D i j)/n) := by
    have h := Real.exp_le_exp.mpr (row i)
    rw [Real.exp_add] at h
    have h1 : 1 ≤ Real.exp ((∑ j, D i j)/n + B) := Real.one_le_exp (by
      dsimp [B]; exact add_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ ↦ posD _ _) hn0.le) (mul_nonneg hn0.le hL))
    rw [Real.exp_add] at h1
    nlinarith
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i _ ↦ show 0 ≤ 1 + 2 * Real.exp (-x i) by positivity) (fun i _ ↦ factor i)
  change _ * (∏ i, (1 + 2 * Real.exp (-x i))) ≤ _
  refine (mul_le_mul_of_nonneg_left hp (by positivity)).trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [← Real.exp_sum, ← Finset.sum_div, sumD]
  rw [show ∀ a c e : ℝ, a * (c * e) = c * (a*e) by intros; ring,
    mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  simp only [Finset.sum_div, ← Finset.sum_add_distrib, w]
  apply Finset.sum_congr rfl
  intros
  ring

theorem unit_ball_qr_product_siegel_integrable (d : ℕ) (hd : 1 ≤ d) :
    (∫⁻ g in columnSiegelSet (d+1), unitBallQRBound d g ∂groupHaar (d+1)) ≠ ⊤ :=
  unitBallQRIntegral_of_decay d hd (qrDecay d hd)

#print axioms unit_ball_qr_product_siegel_integrable
end SigabaNeo.Rogers
