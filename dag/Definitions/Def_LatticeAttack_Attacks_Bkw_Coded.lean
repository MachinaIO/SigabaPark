import Definitions.Def_LatticeAttack_Attacks_Bkw_Recover

set_option autoImplicit true

open MeasureTheory ComplexConjugate SigabaNeo.DualMoments
open scoped Matrix

namespace SigabaNeo.Lattices.Attacks.Bkw

variable {q b k N : ℕ} [NeZero q]
  [MeasurableSpace (ZMod q)] [MeasurableSingletonClass (ZMod q)]

noncomputable def codedLaw (μ : Measure (ZMod q)) (ν : Measure (Residues q b))
    (t : Residues q b) : Measure (ZMod q) :=
  (μ.prod ν).map (fun x ↦ x.1 + t ⬝ᵥ x.2)

variable (μ : Measure (ZMod q)) (ν : Measure (Residues q b)) (t : Residues q b)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem coded_mean :
    ∫ z, ZMod.stdAddChar z ∂(codedLaw μ ν t) =
      (∫ z, ZMod.stdAddChar z ∂μ) * ∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν := by
  rw [codedLaw, integral_map (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable]
  simp only [AddChar.map_add_eq_mul]
  exact integral_prod_mul (fun z ↦ ZMod.stdAddChar z) (fun d ↦ ZMod.stdAddChar (t ⬝ᵥ d))

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem coded_real_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (he : (∫ z, ZMod.stdAddChar z ∂μ).im = 0)
    (hd : (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).im = 0)
    (hμ : a ≤ (∫ z, ZMod.stdAddChar z ∂μ).re)
    (hν : c ≤ (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).re) :
    a * c ≤ (∫ z, ZMod.stdAddChar z ∂(codedLaw μ ν t)).re := by
  rw [coded_mean, Complex.mul_re, he, hd]
  simpa using mul_le_mul hμ hν hc (ha.trans hμ)

omit [MeasurableSpace (ZMod q)] [MeasurableSingletonClass (ZMod q)] in
private theorem char_neg (z : ZMod q) : ZMod.stdAddChar (-z) = conj (ZMod.stdAddChar z) := by
  rw [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

omit [IsProbabilityMeasure ν] in
theorem residual_symmetric_real (hs : ∀ d : Residues q b, ν {d} = ν {-d}) :
    (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).im = 0 := by
  have hm : ν.map Neg.neg = ν := by
    apply Measure.ext_of_singleton
    intro d
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    simpa using (hs d).symm
  have h := integral_map (μ := ν) (φ := Neg.neg) (measurable_of_finite _).aemeasurable
    (f := fun d ↦ ZMod.stdAddChar (t ⬝ᵥ d)) (measurable_of_finite _).aestronglyMeasurable
  rw [hm] at h
  simp only [dotProduct_neg, char_neg, integral_conj] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

omit [MeasurableSingletonClass (ZMod q)] [IsProbabilityMeasure ν] in
theorem residual_difference_mean :
    ∫ x : Residues q b × Residues q b, ZMod.stdAddChar (t ⬝ᵥ (x.1 - x.2)) ∂(ν.prod ν) =
      (‖∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν‖ ^ 2 : ℝ) := by
  simp only [sub_eq_add_neg, dotProduct_add, dotProduct_neg, AddChar.map_add_eq_mul, char_neg]
  rw [integral_prod_mul (fun d ↦ ZMod.stdAddChar (t ⬝ᵥ d))
    (fun d ↦ conj (ZMod.stdAddChar (t ⬝ᵥ d))), integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [MeasurableSingletonClass (ZMod q)] [IsProbabilityMeasure ν] in
theorem residual_difference_nonneg :
    0 ≤ (∫ x : Residues q b × Residues q b,
      ZMod.stdAddChar (t ⬝ᵥ (x.1 - x.2)) ∂(ν.prod ν)).re := by
  rw [residual_difference_mean, Complex.ofReal_re]
  exact sq_nonneg _

theorem coded_recovery (s : Residues q k) (R : Measure (Residues q k)) [IsProbabilityMeasure R]
    (hR : ∀ r, R.real {r} = (Fintype.card (Residues q k) : ℝ)⁻¹)
    {c_err c_code : ℝ} (ha : 0 < c_err) (hc : 0 < c_code)
    (he : (∫ z, ZMod.stdAddChar z ∂μ).im = 0)
    (hd : (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).im = 0)
    (hμ : c_err ≤ (∫ z, ZMod.stdAddChar z ∂μ).re)
    (hν : c_code ≤ (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).re) :
    let c := c_err * c_code
    (Measure.pi (fun _ : Fin N ↦ R.prod (codedLaw μ ν t))).real
        {x | {u | x ∈ accept (N := N) s u c} ≠ ({s} : Set (Residues q k))} ≤
      (q : ℝ)^k * Real.exp (-(N : ℝ) * c^2 / 8) := by
  intro c
  let _ : IsProbabilityMeasure (codedLaw μ ν t) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).2 inferInstance
  have hl := coded_real_lower μ ν t ha.le hc.le he hd hμ hν
  have h := bkwFinal_recovery (N := N) s R (codedLaw μ ν t) hR (mul_pos ha hc)
    (hl.trans_eq (integral_re (𝕜 := ℂ) (f := fun z ↦ ZMod.stdAddChar z) Integrable.of_finite).symm)
  convert h using 1
  simp only [Residues, Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  congr 2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by positivity
    dsimp [c]
    field_simp
    ring

#print axioms coded_mean
#print axioms coded_real_lower
#print axioms residual_symmetric_real
#print axioms residual_difference_mean
#print axioms residual_difference_nonneg
#print axioms coded_recovery

end SigabaNeo.Lattices.Attacks.Bkw
