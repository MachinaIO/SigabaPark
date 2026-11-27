import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Split

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

private def pairEval {n : ℕ} (v : orderTwoIndependent n) (g : SL n) (i : Fin 2) : E n :=
  WithLp.toLp 2 (g • fun j ↦ ((v.val i).val j : ℝ))

private theorem measurable_pairEval {n : ℕ} (v : orderTwoIndependent n) :
    Measurable (pairEval v) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Measurable.of_eval
  intro i
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec (fun j ↦ ((v.val i).val j : ℝ)))
  unfold Matrix.mulVec dotProduct
  fun_prop

def independentPairMeasure {n : ℕ} (D : Set (SL n)) : Measure (Fin 2 → E n) :=
  Measure.sum fun v : orderTwoIndependent n ↦ ((groupHaar n).restrict D).map (pairEval v)

theorem independentPairMeasure_lintegral {n : ℕ} (D : Set (SL n))
    (u : (Fin 2 → E n) → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ x, u x ∂independentPairMeasure D =
      ∑' v : orderTwoIndependent n, orderTwoOrbit D u v.val := by
  rw [independentPairMeasure, lintegral_sum_measure]
  exact tsum_congr fun v ↦ lintegral_map hu (measurable_pairEval v)

private def actPair {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : orderTwoIndependent n) : orderTwoIndependent n :=
  ⟨fun i ↦ ⟨a • (v.val i).val, fun h ↦ (v.val i).property ((MulAction.injective a)
    (h.trans (Matrix.mulVec_zero a.val).symm))⟩,
    (a.toLin'.linearIndependent_iff (LinearMap.ker_eq_bot.mpr a.toLin'.injective)).mpr v.property⟩

private def pairEquiv {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    orderTwoIndependent n ≃ orderTwoIndependent n where
  toFun := actPair a
  invFun := actPair a⁻¹
  left_inv _ := Subtype.ext (funext fun _ ↦ Subtype.ext (inv_smul_smul a _))
  right_inv _ := Subtype.ext (funext fun _ ↦ Subtype.ext (smul_inv_smul a _))

private def workload {n : ℕ} (u : (Fin 2 → E n) → ℝ≥0∞) (x : SL n) :=
  ∑' v : orderTwoIndependent n, u (pairEval v x)

private theorem workload_inv {n : ℕ} (u : (Fin 2 → E n) → ℝ≥0∞) (a : (integerGroup n).op)
    (x : SL n) : workload u (a • x) = workload u x := by
  obtain ⟨b,hb⟩ := (show a.val.unop ∈ integerGroup n from a.property)
  unfold workload
  rw [← (pairEquiv b).tsum_eq (fun v ↦ u (pairEval v x))]
  apply tsum_congr
  intro v
  apply congrArg u
  funext i
  change WithLp.toLp 2 ((x * a.val.unop) • _) = _
  rw [← hb, mul_smul]
  apply congrArg (fun w ↦ WithLp.toLp 2 (x • w))
  exact funext fun j ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) b.val (v.val i).val j).symm

private theorem integral_workload {n : ℕ} (D : Set (SL n)) (u : (Fin 2 → E n) → ℝ≥0∞)
    (hu : Measurable u) : ∫⁻ x, u x ∂independentPairMeasure D =
      ∫⁻ x in D, workload u x ∂groupHaar n := by
  rw [independentPairMeasure_lintegral D u hu]
  symm
  exact lintegral_tsum fun v ↦ (hu.comp (measurable_pairEval v)).aemeasurable

theorem independentPairMeasure_sl_invariant {n : ℕ} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (g : SL n) :
    Measure.map (fun x : Fin 2 → E n ↦ fun i ↦ WithLp.toLp 2 (g • WithLp.ofLp (x i)))
      (independentPairMeasure D) = independentPairMeasure D := by
  let A := fun x : Fin 2 → E n ↦ fun i ↦ WithLp.toLp 2 (g • WithLp.ofLp (x i))
  have hA : Measurable A := by
    apply Measurable.of_eval
    intro i
    have h : Continuous (fun z ↦ g.val.mulVec z) := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact ((PiLp.continuous_toLp 2 _).comp
      (h.comp ((PiLp.continuous_ofLp 2 _).comp (continuous_apply i)))).measurable
  have : Countable (Matrix (Fin n) (Fin n) ℤ) := inferInstanceAs (Countable (Fin n → Fin n → ℤ))
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace (SL n) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar n).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL n)).IsMulLeftInvariant
  let e := MeasurableEquiv.mulLeft g
  have hd' := hd.image_of_equiv e.toEquiv
    (measurePreserving_mul_left (groupHaar n) g⁻¹).quasiMeasurePreserving
    (Equiv.refl _) (fun a x ↦ (mul_assoc g x a.val.unop).symm)
  apply Measure.ext_of_lintegral
  intro u hu
  rw [lintegral_map hu hA]
  change (∫⁻ x, (u ∘ A) x ∂independentPairMeasure D) = _
  rw [integral_workload D _ (hu.comp hA), integral_workload D u hu]
  have he (x : SL n) : workload (u ∘ A) x = workload u (e x) := by
    unfold workload
    apply tsum_congr
    intro v
    apply congrArg u
    funext i
    simp [A, e, pairEval, mul_smul]
  change (∫⁻ x in D, workload (u ∘ A) x ∂_) = _
  simp_rw [he]
  exact ((measurePreserving_mul_left (groupHaar n) g).setLIntegral_comp_emb
    e.measurableEmbedding (workload u) D).trans (hd'.setLIntegral_eq hd _ (workload_inv u))

private theorem castPair_independent {n : ℕ} (v : orderTwoIndependent n) :
    LinearIndependent ℝ (fun i j ↦ ((v.val i).val j : ℝ)) := by
  let z := fun i j ↦ (v.val i).val j
  obtain ⟨j,hj⟩ : ∃ j, z 0 j ≠ 0 := by
    by_contra! h
    exact (v.val 0).property (funext h)
  obtain ⟨k,hk⟩ : ∃ k, z 0 j * z 1 k ≠ z 1 j * z 0 k := by
    by_contra! h
    have H := Fintype.linearIndependent_iff.mp v.property ![-z 1 j, z 0 j]
    apply hj (H ?_ 1)
    funext k
    change (∑ i : Fin 2, ![-z 1 j, z 0 j] i • z i) k = 0
    simp [Fin.sum_univ_two]
    linarith [h k]
  have hdet : (z 0 j : ℝ) * z 1 k ≠ (z 1 j : ℝ) * z 0 k := by exact_mod_cast hk
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have rel (l : Fin n) : c 0 * (z 0 l : ℝ) + c 1 * (z 1 l : ℝ) = 0 := by
    simpa [Fin.sum_univ_two, z] using congrFun hc l
  have det := sub_ne_zero.mpr hdet
  fin_cases i
  · apply (mul_eq_zero.mp (show c 0 * _ = 0 by
      linear_combination (z 1 k : ℝ) * rel j - (z 1 j : ℝ) * rel k)).resolve_right det
  · apply (mul_eq_zero.mp (show c 1 * _ = 0 by
      linear_combination (z 0 j : ℝ) * rel k - (z 0 k : ℝ) * rel j)).resolve_right det

/-- The independent integer orbit measure gives full measure to real two-frames. -/
theorem independentPairMeasure_ae_independent {n : ℕ} (D : Set (SL n)) :
    ∀ᵐ x ∂independentPairMeasure D, LinearIndependent ℝ x := by
  rw [independentPairMeasure, Measure.ae_sum_iff]
  intro v
  rw [ae_map_iff (measurable_pairEval v).aemeasurable
    isOpen_setOfPred_linearIndependent.measurableSet]
  apply Filter.Eventually.of_forall
  intro g
  let e := g.toLin'.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  exact (e.linearIndependent_iff (LinearMap.ker_eq_bot.mpr e.injective)).mpr
    (castPair_independent v)

#print axioms independentPairMeasure_ae_independent
#print axioms independentPairMeasure_sl_invariant
end SigabaNeo.Rogers
