import Definitions.Def_LatticeAttack_Attacks_Dual
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance

set_option autoImplicit true

open scoped Matrix

namespace SigabaNeo.DualMoments

open MeasureTheory ProbabilityTheory

/-- With q = 2, zero matrix, and deterministic w = e = 1, the bias is negative. -/
theorem negative_binary_phase :
    ¬ (2 : ℤ) ∣ 1 ∧
    |Real.cos (2 * Real.pi * 1 * 1 / 2)| = 1 ∧
    Real.cos (2 * Real.pi * 1 * 1 / 2) = -1 := by
  norm_num [show 2 * Real.pi * 1 * 1 / 2 = Real.pi by ring]

variable {q m N : ℕ} [NeZero q]
abbrev Residues (q m : ℕ) := Fin m → ZMod q

noncomputable def dotCharacter (w : Residues q m) : AddChar (Residues q m) ℂ where
  toFun b := ZMod.stdAddChar (∑ j, w j * b j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

theorem uniform_character_mean (w : Residues q m) (hw : w ≠ 0) :
    moment (fun _ : Residues q m ↦ (Fintype.card (Residues q m) : ℝ)⁻¹)
      (fun b ↦ (dotCharacter w b).re) = 0 := by
  classical
  have hn : dotCharacter w ≠ 0 := by
    intro h
    apply hw
    funext j
    have he := DFunLike.congr_fun h (Pi.single j 1)
    change ZMod.stdAddChar (∑ k, w k * Pi.single j 1 k) = 1 at he
    rw [← (ZMod.stdAddChar (N := q)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff] at he
    simpa [Pi.single_apply, mul_ite] using he
  simp [moment, ← Finset.mul_sum, ← Complex.re_sum, AddChar.sum_eq_zero_iff_ne_zero.mpr hn]

theorem signed_score_mean {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (θ : Fin N → Ω → ℝ) {ε : ℝ} (h : ∀ i, ε ≤ moment p (fun x ↦ Real.cos (θ i x))) :
    N * ε ≤ moment p (score θ) := by
  rw [moment_score]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ h i)

theorem fresh_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Fin N → Ω → ℝ} (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ x ∂μ, X i x ∈ Set.Icc (-1) 1) :
    variance (∑ i, X i) μ ≤ N := by
  rw [IndepFun.variance_sum (fun i _ ↦ memLp_of_bounded (hb i) (hm i).aestronglyMeasurable 2)
    (fun i _ j _ hij ↦ hi.indepFun hij)]
  have h (i : Fin N) : variance (X i) μ ≤ 1 := by
    simpa using variance_le_sq_of_bounded (hb i) (hm i)
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ h i)

/-- Cancellation of the noiseless term is pointwise, for every secret. -/
theorem kernel_phase {n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q))
    (w e : Residues q m) (s : Residues q n) (hw : Matrix.vecMul w A = 0) :
    dotCharacter w (A.mulVec s + e) = dotCharacter w e := by
  rw [AddChar.map_add_eq_mul]
  change ZMod.stdAddChar (w ⬝ᵥ A.mulVec s) * _ = _
  simp [Matrix.dotProduct_mulVec, hw]

/-- One multiplication for each summand of each modular dot product. -/
theorem dot_product_multiplications :
    (∑ _ : Fin N, ∑ _ : Fin m, 1 : ℕ) = N * m := by simp

/-- Upper-tail error for fresh bounded observations with a common upper bound on the means. -/
theorem fresh_upper_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Fin N → Ω → ℝ} (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ x ∂μ, X i x ∈ Set.Icc (-1) 1)
    {a t : ℝ} (ha : ∀ i, ∫ x, X i x ∂μ ≤ a) (ht : 0 ≤ t) :
    μ.real {x | N * a + t ≤ ∑ i, X i x} ≤ Real.exp (-t ^ 2 / (2 * N)) := by
  let Y (i : Fin N) (x : Ω) := X i x - ∫ z, X i z ∂μ
  have hy : iIndepFun Y μ :=
    hi.comp (fun i z ↦ z - ∫ x, X i x ∂μ) (fun _ ↦ measurable_id.sub_const _)
  have hg (i : Fin N) : HasSubgaussianMGF (Y i) 1 μ := by
    convert hasSubgaussianMGF_of_mem_Icc (hm i) (hb i) using 1
    norm_num
  have hμ : ∑ i, (∫ x, X i x ∂μ) ≤ N * a := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ ha i)
  apply le_trans (measureReal_mono (μ := μ) (s₂ := {x | t ≤ ∑ i, Y i x}) ?_)
  · simpa using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hy
      (s := Finset.univ) (fun i _ ↦ hg i) ht
  · intro x hx
    change N * a + t ≤ ∑ i, X i x at hx
    change t ≤ ∑ i, (X i x - ∫ z, X i z ∂μ)
    rw [Finset.sum_sub_distrib]
    linarith

/-- Acceptance-probability gap for fresh independent trials under each law. -/
theorem fresh_advantage {Ω : Type*} [MeasurableSpace Ω] {P U : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure U] {X : Fin N → Ω → ℝ}
    (hP : iIndepFun X P) (hU : iIndepFun X U) (hm : ∀ i, Measurable (X i))
    (hb : ∀ i x, X i x ∈ Set.Icc (-1) 1) {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ)
    (hn : 0 < N) (hs : 8 * Real.log (1 / δ) / ε ^ 2 ≤ N)
    (hp : ∀ i, ε ≤ ∫ x, X i x ∂P) (hu : ∀ i, ∫ x, X i x ∂U = 0) :
    let accept := {x | N * ε / 2 ≤ ∑ i, X i x}
    1 - 2 * δ ≤ P.real accept - U.real accept := by
  dsimp only
  let t : ℝ := N * ε / 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast hn
  have hδ : Real.exp (-t ^ 2 / (2 * N)) ≤ δ := by
    rw [← Real.exp_log hd, Real.exp_le_exp]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (sq_pos_of_pos he), one_div, Real.log_inv] at hs
    dsimp [t]
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hs)]
  have hfalse := fresh_upper_tail hU (fun i ↦ (hm i).aemeasurable)
    (fun i ↦ ae_of_all _ (hb i)) (fun i ↦ (hu i).le) ht
  simp only [mul_zero, zero_add] at hfalse
  have hind : iIndepFun (fun i x ↦ -X i x) P :=
    hP.comp (fun _ z ↦ -z) (fun _ ↦ measurable_neg)
  have hl := fresh_upper_tail hind (fun i ↦ (hm i).neg.aemeasurable)
    (fun i ↦ ae_of_all _ fun x ↦
      show -1 ≤ -X i x ∧ -X i x ≤ 1 from ⟨by linarith [(hb i x).2], by linarith [(hb i x).1]⟩)
    (a := -ε) (fun i ↦ by rw [integral_neg]; exact neg_le_neg (hp i)) ht
  let A := {x | t ≤ ∑ i, X i x}
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  have hmiss : P.real Aᶜ ≤ Real.exp (-t ^ 2 / (2 * N)) := by
    apply le_trans (measureReal_mono (μ := P) _) hl
    intro x hx
    change ¬ t ≤ ∑ i, X i x at hx
    change N * -ε + t ≤ ∑ i, -X i x
    rw [Finset.sum_neg_distrib]
    dsimp [t] at *
    linarith
  rw [measureReal_compl hA, probReal_univ] at hmiss
  change 1 - 2 * δ ≤ P.real A - U.real A
  change U.real A ≤ _ at hfalse
  linarith

/-- Fresh dual directions and fresh right-hand sides for a fixed public matrix and secret.
The finite variable W indexes the law of the reduced dual directions. -/
theorem fresh_dual_test {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    {n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Residues q n)
    (w : W → Residues q m) (hnz : ∀ k, w k ≠ 0) (hk : ∀ k, Matrix.vecMul (w k) A = 0)
    (D : Measure W) (E B : Measure (Residues q m))
    [IsProbabilityMeasure D] [IsProbabilityMeasure E] [IsProbabilityMeasure B]
    (hB : ∀ b, B.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ) (hn : 0 < N)
    (hs : 8 * Real.log (1 / δ) / ε ^ 2 ≤ N)
    (hbias : ε ≤ ∫ k, ∫ e, (dotCharacter (w k) e).re ∂E ∂D) :
    let law := fun ν : Measure (Residues q m) ↦ Measure.pi (fun _ : Fin N ↦ D.prod ν)
    let accept := fun (offset : Residues q m) ↦
      {x : Fin N → W × Residues q m |
        N * ε / 2 ≤ ∑ i, (dotCharacter (w (x i).1) (offset + (x i).2)).re}
    1 - 2 * δ ≤ (law E).real (accept (A.mulVec s)) - (law B).real (accept 0) := by
  classical
  dsimp only
  simp only [kernel_phase A _ _ s (hk _), zero_add]
  let f (z : W × Residues q m) := (dotCharacter (w z.1) z.2).re
  have hm : Measurable f := measurable_of_finite _
  refine fresh_advantage (P := Measure.pi (fun _ : Fin N ↦ D.prod E))
    (U := Measure.pi (fun _ : Fin N ↦ D.prod B)) (X := fun i x ↦ f (x i))
    (iIndepFun_pi (fun _ ↦ hm.aemeasurable)) (iIndepFun_pi (fun _ ↦ hm.aemeasurable))
    (fun i ↦ hm.comp (measurable_pi_apply i)) ?_ he hd hn hs ?_ ?_
  · intro i x
    apply abs_le.mp
    exact (Complex.abs_re_le_norm _).trans (by simp [f, dotCharacter, ZMod.stdAddChar_apply])
  · intro i
    rw [integral_comp_eval hm.aestronglyMeasurable, integral_prod f Integrable.of_finite]
    exact hbias
  · intro i
    rw [integral_comp_eval hm.aestronglyMeasurable, integral_prod f Integrable.of_finite]
    have hz (k : W) : ∫ b, f (k, b) ∂B = 0 := by
      rw [integral_fintype Integrable.of_finite]
      simpa only [hB, smul_eq_mul, moment, f] using uniform_character_mean (w k) (hnz k)
    simp [hz]

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.negative_binary_phase
#print axioms SigabaNeo.DualMoments.uniform_character_mean
#print axioms SigabaNeo.DualMoments.signed_score_mean
#print axioms SigabaNeo.DualMoments.fresh_variance
#print axioms SigabaNeo.DualMoments.kernel_phase
#print axioms SigabaNeo.DualMoments.dot_product_multiplications
#print axioms SigabaNeo.DualMoments.fresh_upper_tail

#print axioms SigabaNeo.DualMoments.fresh_advantage
#print axioms SigabaNeo.DualMoments.fresh_dual_test
