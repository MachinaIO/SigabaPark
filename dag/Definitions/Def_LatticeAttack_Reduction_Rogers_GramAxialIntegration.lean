module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_GramInduction

set_option autoImplicit true

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace SigabaNeo.Rogers.Gram

private theorem axial_product_integral (s : ℕ) (μ : Fin s → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, ∏ i, w (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ t, w t ∂μ i := by
  induction s with
  | zero => simp [Measure.pi_empty_univ]
  | succ s ih =>
    rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp (by fun_prop)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [← ih (fun i ↦ μ i.succ)]
    apply lintegral_prod_mul (g := fun x : Fin s → ℝ ↦ ∏ i, w (x i)) hw.aemeasurable
    apply Measurable.aemeasurable
    fun_prop

private theorem axial_pi_density (s : ℕ) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    [SigmaFinite (volume.withDensity w)] :
    Measure.pi (fun _ : Fin s ↦ volume.withDensity w) =
      volume.withDensity (fun a ↦ ∏ i, w (a i)) := by
  apply Measure.pi_eq
  intro t ht
  rw [withDensity_apply _ (MeasurableSet.univ_pi ht), volume_pi, Measure.restrict_pi_pi]
  simp_rw [withDensity_apply _ (ht _)]
  exact axial_product_integral _ _ _ hw

private theorem measurable_gramDomain (s : ℕ) : MeasurableSet (gramDomain s) := by
  have hc : Continuous (@correlation s) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold correlation
    split_ifs <;> fun_prop
  have he : gramDomain s =
      {x | (correlation x).conjTranspose = correlation x} ∩
      ⋂ v : Fin s → ℝ, {x | 0 ≤ dotProduct v ((correlation x).mulVec v)} := by
    ext x
    simp [gramDomain, Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [he]
  exact ((isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun v ↦
    isClosed_le continuous_const (continuous_const.dotProduct
      (hc.matrix_mulVec continuous_const)))).measurableSet

private theorem measurable_gramDensity (n s : ℕ) : Measurable (@gramDensity s n) := by
  classical
  have hc : Continuous (@correlation s) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold correlation
    split_ifs <;> fun_prop
  have hp : {x : OffDiagonal s → ℝ | (correlation x).PosDef} =
      gramDomain s ∩ {x | (correlation x).det ≠ 0} := by
    ext x
    exact ⟨fun h ↦ ⟨h.posSemidef, h.det_pos.ne'⟩, fun ⟨h,hd⟩ ↦
      (show (correlation x).PosSemidef from h).posDef_iff_det_ne_zero.mpr hd⟩
  have hd := hc.matrix_det.measurable
  apply Measurable.ite _ (by fun_prop) measurable_const
  rw [hp]
  exact (measurable_gramDomain s).inter (isClosed_eq hc.matrix_det continuous_const).measurableSet.compl

private theorem radius_prod_pow {s : ℕ} (r : Fin s → ℝ) (hr : ∀ i, 0 ≤ r i) (q : ℝ) :
    (∏ i, r i) ^ q = ∏ i, (r i) ^ q := by
  generalize (Finset.univ : Finset (Fin s)) = u
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    simp [hi, Real.mul_rpow (hr i) (Finset.prod_nonneg fun j _ ↦ hr j), ih]

theorem density_recursion (m s : ℕ) (hs : 1 ≤ s) (hm : s+2 ≤ m) : DensityRecursion m s := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  intro F hF
  let p := (((m:ℝ)+1-3)/2)
  have hp : -1 < p := by
    dsimp [p]
    have : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    linarith
  have hw : Measurable (weight p) := Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const
  let : IsProbabilityMeasure (volume.withDensity (weight p)) := ⟨by
    rw [withDensity_apply _ .univ, setLIntegral_univ, weight_integral hp]⟩
  have hd (n s : ℕ) := (measurable_gramDensity n s).ennreal_ofReal
  let E := splitGram (k+1)
  let T := fun (a : Fin (k+1) → ℝ) (x : OffDiagonal (k+1) → ℝ) ij ↦
    angularThird (a ij.val.1) (a ij.val.2) (x ij)
  have hT : Measurable (fun z : (Fin (k+1) → ℝ) × (OffDiagonal (k+1) → ℝ) ↦
      F (z.1,T z.1 z.2)) := hF.comp (by dsimp [T,angularThird]; fun_prop)
  let : SFinite (densityLaw m (k+1)) := by unfold densityLaw; infer_instance
  change (∫⁻ x, F (E x) ∂densityLaw _ _) =
    ∫⁻ a, ∫⁻ x, F (a,T a x) ∂densityLaw m (k+1) ∂Measure.pi (fun _ ↦ volume.withDensity (weight p))
  rw [axial_pi_density _ _ hw, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (by exact hT.lintegral_prod_right)]
  unfold densityLaw
  simp only [Pi.mul_apply]
  rw [lintegral_withDensity_eq_lintegral_mul volume (hd (m+1) (k+1+1)) (g := fun x ↦ F (E x)) (hF.comp E.measurable),
    ← (splitGram_volume (k+1)).symm.lintegral_comp (by fun_prop)]
  simp only [E, Pi.mul_apply, MeasurableEquiv.apply_symm_apply]
  rw [show (volume : Measure ((Fin (k+1) → ℝ) × (OffDiagonal (k+1) → ℝ))) = volume.prod volume from rfl,
    lintegral_prod (fun z ↦ ENNReal.ofReal (gramDensity (m+1) ((splitGram (k+1)).symm z)) * F z) (((hd (m+1) (k+1+1)).comp (splitGram _).symm.measurable).mul hF).aemeasurable]
  apply lintegral_congr
  intro a
  rw [lintegral_withDensity_eq_lintegral_mul volume (hd m (k+1)) (g := fun x ↦ F (a,T a x)) (hT.comp (measurable_const.prodMk measurable_id))]
  by_cases ha : ∀ i, a i ∈ Ioo (-1) 1
  · let r := fun i ↦ Real.sqrt (1 - a i ^ 2)
    have hpos i : 0 < 1 - a i ^ 2 := by
      have := (sq_lt_one_iff_abs_lt_one _).2 (abs_lt.mpr (ha i))
      linarith
    have hr i : 0 < r i := Real.sqrt_pos.2 (hpos i)
    have he i : a i ^ 2 + r i ^ 2 = 1 := by dsimp [r]; rw [Real.sq_sqrt (hpos i).le]; ring
    rw [gramDensity_fiber_integral m k (by omega) a r hr he (fun y ↦ F (a,y)) (hF.comp (measurable_const.prodMk measurable_id))]
    have hn : 0 < normalizer p := by
      unfold normalizer
      exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
        (beta_pos (by linarith) (by linarith)))
    have hwprod : (∏ i, weight p (a i)) = ENNReal.ofReal
        (normalizer p ^ (k+1) * (∏ i, r i) ^ ((m:ℝ)-2)) := by
      simp_rw [weight, ite_eq_left (ha _)]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ mul_nonneg hn.le (Real.rpow_nonneg (hpos i).le _)),
        Finset.prod_mul_distrib, radius_prod_pow r (fun i ↦ (hr i).le)]
      congr 1
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.sq_sqrt (hpos i).le, ← Real.rpow_natCast_mul (hr i).le]
      congr 1
      dsimp [p]
      ring
    rw [hwprod, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hn.le _) (Real.rpow_nonneg
      (Finset.prod_nonneg fun i _ ↦ (hr i).le) _)), mul_assoc]
    congr 3
    congr 1
    funext ij
    simp [T,angularThird,r,Real.sqrt_mul (hpos _).le]
  · obtain ⟨i,hi⟩ := not_forall.mp ha
    have hz : (∏ j, weight p (a j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (show weight p (a i) = 0 by simp [weight,hi])
    simp [gramDensity_eq_zero_outside _ a _ i hi,hz]

theorem spherical_gram_formula_all :
    ∀ n s : ℕ, 2 ≤ s → s + 2 ≤ n → SphericalGramFormula n s :=
  spherical_of_density_recursion density_recursion

#print axioms spherical_gram_formula_all
end SigabaNeo.Rogers.Gram
