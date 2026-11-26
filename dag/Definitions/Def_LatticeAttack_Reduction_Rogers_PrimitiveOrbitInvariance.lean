import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

private def content {n : ℕ} (v : Fin n → ℤ) := Finset.univ.gcd fun i ↦ (v i).natAbs

private theorem content_dvd_act {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : Fin n → ℤ) : content v ∣ content (a • v) := by
  apply Finset.dvd_gcd
  intro i _
  apply Int.natCast_dvd.mp
  change (content v : ℤ) ∣ ∑ j, a.val i j * v j
  exact Finset.dvd_sum fun j _ ↦ dvd_mul_of_dvd_right
    (Int.natCast_dvd.mpr (Finset.gcd_dvd (f := fun i ↦ (v i).natAbs) (Finset.mem_univ j))) _

private def actPrim {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : ContentFiber n 1) : ContentFiber n 1 :=
  ⟨⟨a • v.val.val, fun h ↦ v.val.property ((MulAction.injective a)
    (h.trans (Matrix.mulVec_zero a.val).symm))⟩, by
    change content (a • v.val.val) = 1
    refine Eq.trans (b := content v.val.val) ?_ v.property
    apply Nat.dvd_antisymm _ (content_dvd_act a _)
    simpa using content_dvd_act a⁻¹ (a • v.val.val)⟩

private def primEquiv {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    ContentFiber n 1 ≃ ContentFiber n 1 where
  toFun := actPrim a
  invFun := actPrim a⁻¹
  left_inv _ := Subtype.ext (Subtype.ext (inv_smul_smul a _))
  right_inv _ := Subtype.ext (Subtype.ext (smul_inv_smul a _))

private def workload {n : ℕ} (u : E n → ℝ≥0∞) (x : SL n) :=
  ∑' v : ContentFiber n 1, u (WithLp.toLp 2 (x • fun j ↦ (v.val.val j : ℝ)))

private theorem workload_inv {n : ℕ} (u : E n → ℝ≥0∞) (a : (integerGroup n).op)
    (x : SL n) : workload u (a • x) = workload u x := by
  obtain ⟨b,hb⟩ := (show a.val.unop ∈ integerGroup n from a.property)
  unfold workload
  rw [← (primEquiv b).tsum_eq (fun v ↦ u (WithLp.toLp 2 (x • fun j ↦ (v.val.val j : ℝ))))]
  apply tsum_congr
  intro v
  change u (WithLp.toLp 2 ((x * a.val.unop) • _)) = _
  rw [← hb, mul_smul]
  congr 2
  apply congrArg (x • ·)
  exact funext fun i ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) b.val v.val.val i).symm

private theorem integral_workload {n : ℕ} (D : Set (SL n)) (u : E n → ℝ≥0∞)
    (hu : Measurable u) : ∫⁻ x, u x ∂primitiveOrbitMeasure D =
      ∫⁻ x in D, workload u x ∂groupHaar n := by
  rw [primitiveOrbitMeasure_lintegral D u hu]
  symm
  apply lintegral_tsum
  intro v
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Measurable.aemeasurable
  apply hu.comp
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun x : SL n ↦ x.val.mulVec (fun j ↦ (v.val.val j : ℝ)))
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem primitiveOrbitMeasure_sl_invariant {n : ℕ} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (g : SL n) :
    Measure.map (fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)) (primitiveOrbitMeasure D) =
      primitiveOrbitMeasure D := by
  let A := fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)
  have hA : Measurable A := by
    apply Continuous.measurable
    have h : Continuous (fun z ↦ g.val.mulVec z) := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact (PiLp.continuous_toLp 2 _).comp (h.comp (PiLp.continuous_ofLp 2 _))
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
  change (∫⁻ x, (u ∘ A) x ∂primitiveOrbitMeasure D) = _
  rw [integral_workload D _ (hu.comp hA), integral_workload D u hu]
  have he (x : SL n) : workload (u ∘ A) x = workload u (e x) := by
    unfold workload
    apply tsum_congr
    intro v
    simp [A, e, mul_smul]
  change (∫⁻ x in D, workload (u ∘ A) x ∂_) = _
  simp_rw [he]
  exact ((measurePreserving_mul_left (groupHaar n) g).setLIntegral_comp_emb
    e.measurableEmbedding (workload u) D).trans (hd'.setLIntegral_eq hd _ (workload_inv u))

#print axioms primitiveOrbitMeasure_sl_invariant
end SigabaNeo.Rogers
