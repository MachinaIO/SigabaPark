import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKSplit
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers.Frame

def independent (n k : ℕ) : Set (IntegerTuple n k) :=
  {z | LinearIndependent ℤ (fun i ↦ (z i).val)}

def frameEval {n k : ℕ} (v : independent n k) (g : SL n) (i : Fin k) : E n :=
  WithLp.toLp 2 (g • fun j ↦ ((v.val i).val j : ℝ))

private theorem measurable_frameEval {n k : ℕ} (v : independent n k) :
    Measurable (frameEval v) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Measurable.of_eval
  intro i
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec (fun j ↦ ((v.val i).val j : ℝ)))
  unfold Matrix.mulVec dotProduct
  fun_prop

def frameMeasure {n k : ℕ} (D : Set (SL n)) : Measure (Fin k → E n) :=
  Measure.sum fun v : independent n k ↦ ((groupHaar n).restrict D).map (frameEval v)

theorem frameMeasure_lintegral {n k : ℕ} (D : Set (SL n))
    (u : (Fin k → E n) → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ x, u x ∂frameMeasure (k := k) D =
      ∑' v : independent n k, (∫⁻ g in D, u (frameEval v g) ∂groupHaar n) := by
  rw [frameMeasure, lintegral_sum_measure]
  exact tsum_congr fun v ↦ lintegral_map hu (measurable_frameEval v)

private def actFrame {n k : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : independent n k) : independent n k :=
  ⟨fun i ↦ ⟨a • (v.val i).val, fun h ↦ (v.val i).property ((MulAction.injective a)
    (h.trans (Matrix.mulVec_zero a.val).symm))⟩,
    (a.toLin'.linearIndependent_iff (LinearMap.ker_eq_bot.mpr a.toLin'.injective)).mpr v.property⟩

private def frameEquiv {n k : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    independent n k ≃ independent n k where
  toFun := actFrame a
  invFun := actFrame a⁻¹
  left_inv _ := Subtype.ext (funext fun _ ↦ Subtype.ext (inv_smul_smul a _))
  right_inv _ := Subtype.ext (funext fun _ ↦ Subtype.ext (smul_inv_smul a _))

private def workload {n k : ℕ} (u : (Fin k → E n) → ℝ≥0∞) (x : SL n) :=
  ∑' v : independent n k, u (frameEval v x)

private theorem workload_inv {n k : ℕ} (u : (Fin k → E n) → ℝ≥0∞) (a : (integerGroup n).op)
    (x : SL n) : workload u (a • x) = workload u x := by
  obtain ⟨b,hb⟩ := (show a.val.unop ∈ integerGroup n from a.property)
  unfold workload
  rw [← (frameEquiv b).tsum_eq (fun v ↦ u (frameEval v x))]
  apply tsum_congr
  intro v
  apply congrArg u
  funext i
  change WithLp.toLp 2 ((x * a.val.unop) • _) = _
  rw [← hb, mul_smul]
  apply congrArg (fun w ↦ WithLp.toLp 2 (x • w))
  exact funext fun j ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) b.val (v.val i).val j).symm

private theorem integral_workload {n k : ℕ} (D : Set (SL n)) (u : (Fin k → E n) → ℝ≥0∞)
    (hu : Measurable u) : ∫⁻ x, u x ∂frameMeasure (k := k) D =
      ∫⁻ x in D, workload u x ∂groupHaar n := by
  rw [frameMeasure_lintegral D u hu]
  symm
  exact lintegral_tsum fun v ↦ (hu.comp (measurable_frameEval v)).aemeasurable

theorem frameMeasure_sl_invariant {n k : ℕ} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (g : SL n) :
    Measure.map (fun x : Fin k → E n ↦ fun i ↦ WithLp.toLp 2 (g • WithLp.ofLp (x i)))
      (frameMeasure (k := k) D) = frameMeasure (k := k) D := by
  let A := fun x : Fin k → E n ↦ fun i ↦ WithLp.toLp 2 (g • WithLp.ofLp (x i))
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
  change (∫⁻ x, (u ∘ A) x ∂frameMeasure (k := k) D) = _
  rw [integral_workload D _ (hu.comp hA), integral_workload D u hu]
  have he (x : SL n) : workload (u ∘ A) x = workload u (e x) := by
    unfold workload
    apply tsum_congr
    intro v
    apply congrArg u
    funext i
    simp [A, e, frameEval, mul_smul]
  change (∫⁻ x in D, workload (u ∘ A) x ∂_) = _
  simp_rw [he]
  exact ((measurePreserving_mul_left (groupHaar n) g).setLIntegral_comp_emb
    e.measurableEmbedding (workload u) D).trans (hd'.setLIntegral_eq hd _ (workload_inv u))


theorem rankIndex_last_iff {n k} (z : IntegerTuple n (k+1)) :
    tupleRankIndex (Nat.succ_pos k) z = Fin.last k ↔ z ∈ independent n (k+1) := by
  change _ ↔ LinearIndependent ℤ _
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  change _ ↔ k + 1 = tupleRank z
  have h := tupleRankIndex_succ (Nat.succ_pos k) z
  rw [Fin.ext_iff]
  simp only [Fin.val_last]
  omega

theorem rankOrbitSum_last {n k} (D : Set (SL n)) (F : (Fin (k+1) → E n) → ℝ≥0∞)
    (hF : Measurable F) :
    rankOrbitSum (Nat.succ_pos k) D F (Fin.last k) = ∫⁻ x, F x ∂frameMeasure D := by
  rw [frameMeasure_lintegral D F hF]
  let e := Equiv.subtypeEquivRight (fun z ↦ rankIndex_last_iff (n := n) (k := k) z)
  exact e.tsum_eq (fun v ↦ ∫⁻ g in D, F (frameEval v g) ∂groupHaar n)

theorem frameMeasure_ae_independent {n k : ℕ} (D : Set (SL n)) :
    ∀ᵐ x ∂frameMeasure (k := k) D, LinearIndependent ℝ x := by
  rw [frameMeasure, Measure.ae_sum_iff]
  intro v
  rw [ae_map_iff (measurable_frameEval v).aemeasurable
    isOpen_setOfPred_linearIndependent.measurableSet]
  apply Filter.Eventually.of_forall
  intro g
  let e := g.toLin'.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  exact (e.linearIndependent_iff (LinearMap.ker_eq_bot.mpr e.injective)).mpr
    ((linearIndependent_algebraMap_comp_iff (S := ℝ) (v := fun i ↦ (v.val i).val)).mpr v.property)

end SigabaNeo.Rogers.Frame
