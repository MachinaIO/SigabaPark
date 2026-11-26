import Definitions.Def_LatticeAttack_Attacks_Dual_Assembled

set_option autoImplicit true

open MeasureTheory ProbabilityTheory

namespace SigabaNeo.DualMoments

variable {q m N : ℕ} [NeZero q]
variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

abbrev outsideBox (m : ℕ) (B : ℝ) : Set (Fin m → ℤ) :=
  ⋃ j, {e | B < |(e j : ℝ)|}

theorem outsideBox_prob (P : Measure (Fin m → ℤ)) [IsProbabilityMeasure P]
    {B p : ℝ} (hp : ∀ j : Fin m, P.real {e | B < |(e j : ℝ)|} ≤ p) :
    P.real (outsideBox m B) ≤ m * p := by
  apply (measureReal_iUnion_fintype_le (μ := P) _).trans
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hp j)

abbrev reduceError (q : ℕ) (e : Fin m → ℤ) : Residues q m := fun j ↦ (e j : ZMod q)

noncomputable abbrev boxBias (q m : ℕ) (W₀ B : ℝ) :=
  1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2

theorem truncated_dual_bias (wl : W → Fin m → ℤ) {W₀ B : ℝ}
    (hw : ∀ k, Real.sqrt (∑ j, (wl k j : ℝ) ^ 2) ≤ W₀) (hB : 0 ≤ B)
    (D : Measure W) (P : Measure (Fin m → ℤ)) [IsProbabilityMeasure D] [IsProbabilityMeasure P] :
    boxBias q m W₀ B - 2 * P.real (outsideBox m B) ≤
      ∫ k, ∫ b, (dotCharacter (reduceError q (wl k)) b).re ∂(P.map (reduceError q)) ∂D := by
  classical
  let bad := outsideBox m B
  have hm : MeasurableSet bad := (Set.to_countable bad).measurableSet
  apply le_trans (b := ∫ _ : W, boxBias q m W₀ B - 2 * P.real bad ∂D) (by simp [bad])
  apply integral_mono (integrable_const _) Integrable.of_finite
  intro k
  have hr : Measurable (reduceError q (m := m)) := measurable_of_countable _
  dsimp only
  let g := fun b : Residues q m ↦ (dotCharacter (reduceError q (wl k)) b).re
  rw [integral_map hr.aemeasurable (measurable_of_finite g).aestronglyMeasurable]
  let f := fun e : Fin m → ℤ ↦ Real.cos (2 * Real.pi / q * ∑ j, (wl k j : ℝ) * e j)
  simp only [g, dotCharacter_cast_re]
  have hf : Integrable f P := Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ fun e ↦ Real.abs_cos_le_one _)
  have hi := (integrable_const (2 : ℝ) (μ := P)).indicator hm
  have h := integral_mono (μ := P) ((integrable_const (boxBias q m W₀ B)).sub hi) hf
  have hpt : ∀ e, boxBias q m W₀ B - bad.indicator (fun _ ↦ (2 : ℝ)) e ≤ f e := by
    intro e
    by_cases he : e ∈ bad
    · rw [Set.indicator_of_mem he]
      dsimp [boxBias, f]
      linarith [Real.neg_one_le_cos (2 * Real.pi / q * ∑ j, (wl k j : ℝ) * e j),
        sq_nonneg (2 * Real.pi / q * (W₀ * B * Real.sqrt m))]
    · rw [Set.indicator_of_notMem he, sub_zero]
      have hd := abs_dot_le_of_coordinate_bound _ (fun j ↦ (e j : ℝ)) (hw k) hB
        (fun j ↦ le_of_not_gt fun hj ↦ he (Set.mem_iUnion.mpr ⟨j, hj⟩))
      have hq : 0 ≤ 2 * Real.pi / q := by positivity
      have ha := mul_le_mul_of_nonneg_left hd hq
      rw [← abs_of_nonneg hq, ← abs_mul] at ha
      refine le_trans ?_ Real.one_sub_sq_div_two_le_cos
      dsimp [boxBias]
      rw [abs_of_nonneg hq] at ha
      linarith [sq_le_sq' (neg_le_of_abs_le ha) (le_of_abs_le ha)]
  specialize h hpt
  simpa [Pi.sub_apply, integral_sub (integrable_const _) hi, integral_indicator_const _ hm,
    smul_eq_mul, mul_comm, f] using h

theorem gaussianDualTest {n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Residues q n)
    (wl : W → Fin m → ℤ) (hnz : ∀ k, reduceError q (wl k) ≠ 0)
    (hk : ∀ k, Matrix.vecMul (reduceError q (wl k)) A = 0)
    {W₀ t σ p ε δ : ℝ} (hw : ∀ k, Real.sqrt (∑ j, (wl k j : ℝ) ^ 2) ≤ W₀)
    (hB : 0 ≤ t * σ) (D : Measure W) (P : Measure (Fin m → ℤ)) (U : Measure (Residues q m))
    [IsProbabilityMeasure D] [IsProbabilityMeasure P] [IsProbabilityMeasure U]
    (hp : ∀ j : Fin m, P.real {e | t * σ < |(e j : ℝ)|} ≤ p)
    (hU : ∀ b, U.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    (he : 0 < ε) (hb : ε ≤ boxBias q m W₀ (t * σ) - 2 * (m * p))
    (hd : 0 < δ) (hn : 0 < N) (hs : 8 * Real.log (1 / δ) / ε ^ 2 ≤ N) :
    let law := fun ν : Measure (Residues q m) ↦ Measure.pi (fun _ : Fin N ↦ D.prod ν)
    let accept := fun (offset : Residues q m) ↦ {x : Fin N → W × Residues q m |
      N * ε / 2 ≤ ∑ i, (dotCharacter (reduceError q (wl (x i).1)) (offset + (x i).2)).re}
    1 - 2 * δ ≤ (law (P.map (reduceError q))).real (accept (A.mulVec s)) -
      (law U).real (accept 0) := by
  have := (Measure.isProbabilityMeasure_map_iff (μ := P)
    (measurable_of_countable (reduceError q (m := m))).aemeasurable).2 inferInstance
  apply fresh_dual_test A s _ hnz hk D _ U hU he hd hn hs
  apply le_trans _ (truncated_dual_bias wl hw hB D P)
  linarith [outsideBox_prob P hp]

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.outsideBox_prob
#print axioms SigabaNeo.DualMoments.truncated_dual_bias
#print axioms SigabaNeo.DualMoments.gaussianDualTest
