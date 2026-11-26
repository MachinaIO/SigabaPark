import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyUnfolding
import Definitions.Def_LatticeAttack_Reduction_Rogers_UnitBallQRIntegral
set_option autoImplicit true

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Pointwise
namespace SigabaNeo.Rogers

private theorem measurable_qrProduct (d : ℕ) : Measurable (@qrProduct d) := by
  have h (i : Fin (d+1)) : Measurable (fun t : Fin d → ℝ ↦ Fin.partialSum t i) := by
    induction i using Fin.induction with
    | zero => simp
    | succ k ih => simp only [Fin.partialSum_succ]; exact ih.add (measurable_pi_apply k)
  unfold qrProduct columnDiagLogs
  fun_prop

private theorem privateSqIntegral_of_decay (d : ℕ) (hd : 2 ≤ d)
    (decay : ∃ (A : ℝ) (w : Fin d → ℝ), (∀ i, 0 < w i) ∧
      ∀ t : Fin d → ℝ, (∀ i, -Real.log 2 / 2 ≤ t i) →
        (∏ i, Real.exp (-qrWeight i * t i)) * (qrProduct t)^2 ≤
          A * ∏ i, Real.exp (-w i * t i)) :
    (∫⁻ g in columnSiegelSet (d+1), (unitBallQRBound d g)^2 ∂groupHaar (d+1)) ≠ ⊤ := by
  obtain ⟨A,w,hw,hA⟩ := decay
  let b := -Real.log 2 / 2
  let S : Set (Fin d → ℝ) := univ.pi fun _ ↦ Ici b
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici
  have hq : Measurable (fun t : Fin d → ℝ ↦ ENNReal.ofReal ((qrProduct t)^2)) := ENNReal.measurable_ofReal.comp ((measurable_qrProduct d).pow_const 2)
  have root : (∫⁻ t in S, ENNReal.ofReal ((qrProduct t)^2) ∂columnRootMeasure d) ≠ ⊤ := by
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
    ⟨measurable_gramColumnParameters d, fun g p ↦ ⟨gramParamsRecovered d (by omega) g p,
      fun e ↦ e ▸ gramParamsRealized d (by omega) g⟩⟩
  let : SigmaFinite (columnRootMeasure d) := by unfold columnRootMeasure; infer_instance
  obtain ⟨C,hC⟩ := columnQRHaarPushforward (by omega : 1 ≤ d) chart
  let F (p : ColumnParameters d) := ENNReal.ofReal ((qrProduct p.1)^2)
  have hF : Measurable F := hq.comp measurable_fst
  apply ne_top_of_le_ne_top _ (lintegral_mono_set (columnSiegel_subset_rectangle d))
  unfold unitBallQRBound
  have hv : volume (densityBall (d+1) 0) ≠ 0 := by
    simpa [densityBall] using (Metric.measure_ball_pos (volume : Measure (E (d+1))) 0 one_pos).ne'
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hv)), columnRectangle_preimage chart]
  apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hv))
  have hpow (g : SL (d+1)) : 0 ≤ qrProduct (gramColumnParameters g).1 :=
    Finset.prod_nonneg fun _ _ ↦ by positivity
  change (∫⁻ g in _, (ENNReal.ofReal (qrProduct (gramColumnParameters g).1))^2 ∂groupHaar _) ≠ ⊤
  simp_rw [← ENNReal.ofReal_pow (hpow _)]
  change (∫⁻ g in gramColumnParameters ⁻¹' (S ×ˢ upperCube _), F (gramColumnParameters g)
    ∂groupHaar _) ≠ ⊤
  rw [← setLIntegral_map (hS.prod (show MeasurableSet (upperCube (d+1)) from measurableSet_Icc)) hF chart.1, hC, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  rw [← Measure.prod_restrict, lintegral_prod F hF.aemeasurable]
  simpa [F, lintegral_const, upperCube_volume] using root

end SigabaNeo.Rogers

namespace SigabaNeo.Rogers

private theorem squareDecay (d : ℕ) (hd : 2 ≤ d) :
    ∃ (A : ℝ) (w : Fin d → ℝ), (∀ i, 0 < w i) ∧
      ∀ t : Fin d → ℝ, (∀ i, -Real.log 2 / 2 ≤ t i) →
        (∏ i, Real.exp (-qrWeight i * t i)) * (qrProduct t)^2 ≤
          A * ∏ i, Real.exp (-w i * t i) := by
  classical
  let n : ℝ := d+1
  have hn : 2 < n := by dsimp [n]; exact_mod_cast (by omega : 2 < d+1)
  have hn0 : 0 < n := by linarith
  let L := Real.log 2 / 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let B := n * L
  let w (i : Fin d) := qrWeight i * (1 - 2/n)
  refine ⟨((3 * Real.exp B)^(d+1))^2 * Real.exp (2*((∑ i : Fin d, qrWeight i * L)/n)), w, ?_, ?_⟩
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
  change _ * (∏ i, (1 + 2 * Real.exp (-x i)))^2 ≤ _
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp 2) (by positivity)).trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [← Real.exp_sum, ← Finset.sum_div, sumD]
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [show ∀ a c e : ℝ, a * (c * e) = c * (a*e) by intros; ring,
    mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  simp only [Nat.cast_ofNat, Finset.sum_div, w]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem unit_ball_qr_square_siegel_integrable (d : ℕ) (hd : 2 ≤ d) :
    (∫⁻ g in columnSiegelSet (d+1), (unitBallQRBound d g)^2 ∂groupHaar (d+1)) ≠ ⊤ :=
  privateSqIntegral_of_decay d hd (squareDecay d hd)

#print axioms unit_ball_qr_square_siegel_integrable

/-- The normalized count of nonzero vectors in the unit ball has finite second moment. -/
theorem densityWork_unit_square_finite {n : ℕ} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) :
    (∫⁻ g in D, (densityWork n 0 g)^2 ∂groupHaar n) ≠ ⊤ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let S := columnSiegelSet (d+1)
  let f := fun g : SL (d+1) ↦ (densityWork (d+1) 0 g)^2
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin (d+1))
  have : Countable (Matrix (Fin (d+1)) (Fin (d+1)) ℤ) :=
    inferInstanceAs (Countable (Fin (d+1) → Fin (d+1) → ℤ))
  have : Countable (Matrix.SpecialLinearGroup (Fin (d+1)) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup (d+1)) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup (d+1)).op := (integerGroup _).equivOp.surjective.countable
  let := groupHaar_rightInvariant (d+1)
  let : BorelSpace (SL (d+1)) := ⟨rfl⟩
  have inv (γ : (integerGroup (d+1)).op) (x : SL (d+1)) : f (γ • x) = f x := by
    dsimp [f, densityWork]
    rw [show QuotientGroup.mk (γ • x) = QuotientGroup.mk x from
      QuotientGroup.mk_mul_of_mem x γ.property]
  have bound : (∫⁻ g in D, f g ∂groupHaar _) ≤ ∫⁻ g in S, f g ∂groupHaar _ := by
    rw [hd.setLIntegral_eq_tsum' f S]
    simp only [inv]
    refine (lintegral_mono_set (t := ⋃ γ : (integerGroup (d+1)).op, γ • S ∩ D) ?_).trans
      (lintegral_iUnion_le _ _)
    intro x hx
    obtain ⟨γ,hγ⟩ := column_siegel_arithmetic_cover d (by omega) x
    exact mem_iUnion.mpr ⟨γ,hγ,hx⟩
  exact ne_top_of_le_ne_top (unit_ball_qr_square_siegel_integrable d (by omega))
    (bound.trans (lintegral_mono fun g ↦ pow_le_pow_left' (unit_ball_work_le_qr_product d (by omega) g) 2))

#print axioms densityWork_unit_square_finite

/-- The square of the normalized expanding-ball count calibrates the total pair workload. -/
theorem densityWork_square_limit {n : ℕ} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hfin : groupHaar n D ≠ ⊤) :
    Filter.Tendsto (fun j ↦ ∫⁻ g in D, (densityWork n j g)^2 ∂groupHaar n)
      Filter.atTop (nhds (groupHaar n D)) := by
  obtain ⟨C,hC⟩ := siegel_density_residue_class_bound n (by omega)
  let b := fun g : SL n ↦ (C : ℝ≥0∞)^2 * (2 + 2 * (densityWork n 0 g)^2)
  have hm (j : ℕ) : Measurable (densityWork n j) :=
    (tupleWorkload_measurable ((densityTest_measurable n j).comp (measurable_pi_apply 0))).comp
      measurable_quotient_mk''
  have hb : (∫⁻ g in D, b g ∂groupHaar n) ≠ ⊤ := by
    dsimp only [b]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      lintegral_add_left measurable_const, setLIntegral_const,
      lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hfin,
      ENNReal.mul_ne_top (by norm_num) (densityWork_unit_square_finite hn hd)⟩
  have bound (j : ℕ) (g : SL n) : (densityWork n j g)^2 ≤ b g := by
    refine (pow_le_pow_left' (hC j g) 2).trans ?_
    rw [mul_pow]
    dsimp only [b]
    gcongr
    generalize densityWork n 0 g = a
    by_cases ha : a = ⊤
    · simp [ha]
    lift a to ℝ≥0 using ha
    exact_mod_cast (show (1+a)^2 ≤ 2 + 2*a^2 by
      exact_mod_cast (show (1+(a:ℝ))^2 ≤ 2+2*(a:ℝ)^2 by nlinarith [sq_nonneg ((a:ℝ)-1)]))
  have lim (g : SL n) := ((ENNReal.continuous_pow 2).tendsto 1).comp (siegel_density_ball_pointwise n (by omega) g)
  simpa using tendsto_lintegral_of_dominated_convergence (μ := (groupHaar n).restrict D)
    (f := fun _ ↦ 1) b (fun j ↦ (hm j).pow_const 2)
    (fun j ↦ Filter.Eventually.of_forall (bound j)) hb (Filter.Eventually.of_forall
      (fun g ↦ by simpa [Function.comp_def] using lim g))

#print axioms densityWork_square_limit
end SigabaNeo.Rogers
