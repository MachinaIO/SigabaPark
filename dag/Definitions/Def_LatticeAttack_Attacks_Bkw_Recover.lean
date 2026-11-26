import Definitions.Def_LatticeAttack_Attacks_Dual_FreshMoments
import Definitions.Def_LatticeAttack_Attacks_Bkw_FourierTest
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit true

/-!
# Final BKW stage: Fourier score test over `ZMod q`, end to end

After the reduction stages, BKW holds `N` fresh samples `(r_i, b_i = r_i·s + z_i)` with `r_i`
uniform on `F_q^k` and `z_i` independent with law `Z` whose real character mean is at least
`c > 0` (for `a+1` stages of a base error law `p`, `signedLaw_real_mean` gives exactly
`c = |p̂(1)|^(2^(a+1))`). The test keeps every candidate `t` with
`Σ_i Re ψ(b_i − r_i·t) ≥ N c / 2`, `ψ = ZMod.stdAddChar`.

`bkwFinal_recovery`: the kept set is exactly `{s}` except with probability
`≤ q^k · exp(−(N c/2)²/(2N)) = q^k exp(−N c²/8)`; `scoreOpCount N q k` operations.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SigabaNeo.Lattices.Attacks.Bkw

open SigabaNeo.DualMoments

variable {q k N : ℕ} [NeZero q]

/-- The score observation of one sample for candidate `t` (written via the hidden pair
`(r, z)`; it equals `Re ψ(b − r·t)` with `b = r·s + z`). -/
noncomputable def obs (s t : Residues q k) (x : Residues q k × ZMod q) : ℝ :=
  (ZMod.stdAddChar (x.1 ⬝ᵥ s + x.2 - x.1 ⬝ᵥ t)).re

noncomputable def accept (s t : Residues q k) (c : ℝ) : Set (Fin N → Residues q k × ZMod q) :=
  {x | N * c / 2 ≤ ∑ i, obs s t (x i)}

theorem obs_bound (s t : Residues q k) (x) : obs s t x ∈ Set.Icc (-1 : ℝ) 1 := by
  apply abs_le.mp
  exact (Complex.abs_re_le_norm _).trans (by simp [ZMod.stdAddChar_apply])

theorem obs_eq (s t : Residues q k) (x : Residues q k × ZMod q) :
    obs s t x = (dotCharacter (s - t) x.1 * ZMod.stdAddChar x.2).re := by
  unfold obs
  congr 1
  change _ = ZMod.stdAddChar (∑ j, (s - t) j * x.1 j) * _
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [show ∑ j, x.1 j * s j = ∑ j, s j * x.1 j from Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _,
    show ∑ j, x.1 j * t j = ∑ j, t j * x.1 j from Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
  ring

variable [MeasurableSpace (ZMod q)] [MeasurableSingletonClass (ZMod q)]
  [MeasurableSingletonClass (Residues q k)]

theorem obs_mean_wrong (s t : Residues q k) (hst : t ≠ s)
    (R : Measure (Residues q k)) (Z : Measure (ZMod q))
    [IsProbabilityMeasure R] [IsProbabilityMeasure Z]
    (hR : ∀ r, R.real {r} = (Fintype.card (Residues q k) : ℝ)⁻¹) :
    ∫ x, obs s t x ∂(R.prod Z) = 0 := by
  rw [integral_prod_symm _ Integrable.of_finite]
  have h (z : ZMod q) : ∫ r, obs s t (r, z) ∂R = 0 := by
    rw [integral_fintype Integrable.of_finite]
    simp only [hR, smul_eq_mul, obs_eq]
    have hd : s - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
    have hn : dotCharacter (s - t) ≠ 0 := by
      intro h
      apply hd
      funext j
      have he := DFunLike.congr_fun h (Pi.single j 1)
      change ZMod.stdAddChar (∑ l, (s - t) l * Pi.single j 1 l) = 1 at he
      rw [← (ZMod.stdAddChar (N := q)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff] at he
      simpa [Pi.single_apply, mul_ite] using he
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul,
      AddChar.sum_eq_zero_iff_ne_zero.mpr hn]
    simp
  simp [h]

theorem obs_mean_right (s : Residues q k) (R : Measure (Residues q k)) (Z : Measure (ZMod q))
    [IsProbabilityMeasure R] [IsProbabilityMeasure Z] :
    ∫ x, obs s s x ∂(R.prod Z) = ∫ z, (ZMod.stdAddChar z).re ∂Z := by
  rw [integral_prod _ Integrable.of_finite]
  simp [obs]

/-- **Final BKW stage, end to end.** -/
theorem bkwFinal_recovery (s : Residues q k) (R : Measure (Residues q k)) (Z : Measure (ZMod q))
    [IsProbabilityMeasure R] [IsProbabilityMeasure Z]
    (hR : ∀ r, R.real {r} = (Fintype.card (Residues q k) : ℝ)⁻¹)
    {c : ℝ} (hc : 0 < c) (hZ : c ≤ ∫ z, (ZMod.stdAddChar z).re ∂Z) :
    (Measure.pi (fun _ : Fin N ↦ R.prod Z)).real
        {x | {t | x ∈ accept (N := N) s t c} ≠ ({s} : Set (Residues q k))} ≤
      Fintype.card (Residues q k) * Real.exp (-(N * c / 2) ^ 2 / (2 * N)) := by
  classical
  set P := Measure.pi (fun _ : Fin N ↦ R.prod Z)
  set e := Real.exp (-(N * c / 2) ^ 2 / (2 * N))
  have hm (t : Residues q k) : Measurable (obs s t) := measurable_of_finite _
  have hind (t : Residues q k) : iIndepFun (fun i x ↦ obs s t (x i)) P :=
    iIndepFun_pi (fun _ ↦ (hm t).aemeasurable)
  have hmean (t : Residues q k) (i : Fin N) :
      ∫ x, obs s t (x i) ∂P = ∫ x, obs s t x ∂(R.prod Z) :=
    integral_comp_eval (hm t).aestronglyMeasurable
  have ht : 0 ≤ N * c / 2 := by positivity
  let bad : Residues q k → Set (Fin N → Residues q k × ZMod q) :=
    fun t ↦ if t = s then (accept s s c)ᶜ else accept s t c
  have hbad (t : Residues q k) : P.real (bad t) ≤ e := by
    by_cases hts : t = s
    · subst hts
      simp only [bad, ite_true]
      have hneg : iIndepFun (fun i x ↦ -obs t t (x i)) P :=
        (hind t).comp (fun _ z ↦ -z) (fun _ ↦ measurable_neg)
      have hl := fresh_upper_tail hneg (fun i ↦ ((hm t).comp (measurable_pi_apply i)).neg.aemeasurable)
        (fun i ↦ ae_of_all _ fun x ↦ show -1 ≤ -obs t t (x i) ∧ -obs t t (x i) ≤ 1 from
          ⟨by linarith [(obs_bound t t (x i)).2], by linarith [(obs_bound t t (x i)).1]⟩)
        (a := -c) (fun i ↦ by
          rw [integral_neg, hmean, obs_mean_right]; exact neg_le_neg hZ) ht
      refine le_trans (measureReal_mono ?_ (measure_ne_top P _)) hl
      intro x hx
      simp only [accept, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      change N * -c + N * c / 2 ≤ ∑ i, -obs t t (x i)
      rw [Finset.sum_neg_distrib]
      linarith
    · simp only [bad, hts, ite_false]
      have hl := fresh_upper_tail (hind t) (fun i ↦ ((hm t).comp (measurable_pi_apply i)).aemeasurable)
        (fun i ↦ ae_of_all _ fun x ↦ obs_bound s t (x i))
        (a := 0) (fun i ↦ by rw [hmean, obs_mean_wrong s t hts R Z hR]) ht
      simpa [accept] using hl
  have hsub : {x | {t | x ∈ accept (N := N) s t c} ≠ ({s} : Set (Residues q k))} ⊆
      ⋃ t ∈ (Finset.univ : Finset (Residues q k)), bad t := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    by_contra hall
    push_neg at hall
    apply hx
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    have := hall t
    by_cases hts : t = s
    · subst hts; simp only [bad, ite_true, Set.mem_compl_iff, not_not] at this; simpa using this
    · simp only [bad, hts, ite_false] at this; simp [this, hts]
  calc _ ≤ P.real (⋃ t ∈ (Finset.univ : Finset (Residues q k)), bad t) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ t, P.real (bad t) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t : Residues q k, e := Finset.sum_le_sum fun t _ ↦ hbad t
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The law of one stage output is the product of a uniform suffix and the signed error law. -/
theorem stagePMF_toMeasure {B : Type} [Fintype B] [Nonempty B] [AddCommGroup B]
    (p : PMF (ZMod q)) (a : ℕ) :
    (stagePMF (B := B) (R := Residues q k) p a).toMeasure =
      (flat (Residues q k)).toMeasure.prod (signedLaw p a).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨r, z⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change stages B (ZMod q) p a (Residues q k) (r, z) = _
  rw [stages_eq, independentPair_apply]

/-- **BKW, end to end (reduction stages + final test).** Feed `N` independent outputs of
`a+1` reduction stages (each a uniform suffix `r` with error `z ~ signedLaw p (a+1)`, by
`stages_iid`) into the final score test. If the base error law has nonzero Fourier coefficient,
`c = ‖p̂(1)‖^(2^(a+1)) > 0`, the kept candidate set is exactly `{s}` except with probability
`≤ q^k · exp(−(N c/2)²/(2N))`. The stage cost is `freshCost` (`= (2|B|)^a`, `freshCost_eq`) per
output and the test costs `scoreOpCount N q k`. -/
theorem bkw_end_to_end {B : Type} [Fintype B] [Nonempty B] [AddCommGroup B]
    (p : PMF (ZMod q)) (a : ℕ) (s : Residues q k)
    (hc : 0 < ‖∑ z, ((p z).toReal : ℂ) * ZMod.stdAddChar z‖ ^ (2 ^ (a + 1))) :
    let c := ‖∑ z, ((p z).toReal : ℂ) * ZMod.stdAddChar z‖ ^ (2 ^ (a + 1))
    (Measure.pi (fun _ : Fin N ↦
        (stagePMF (B := B) (R := Residues q k) p (a + 1)).toMeasure)).real
        {x | {t | x ∈ accept (N := N) s t c} ≠ ({s} : Set (Residues q k))} ≤
      Fintype.card (Residues q k) * Real.exp (-(N * c / 2) ^ 2 / (2 * N)) := by
  intro c
  rw [stagePMF_toMeasure]
  refine bkwFinal_recovery s _ _ (fun r ↦ ?_) hc (le_of_eq ?_)
  · rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [flat, PMF.ofFintype_apply, ENNReal.toReal_inv]
  · rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul, c]
    exact (signedLaw_real_mean p a).symm

end SigabaNeo.Lattices.Attacks.Bkw

#print axioms SigabaNeo.Lattices.Attacks.Bkw.bkwFinal_recovery
#print axioms SigabaNeo.Lattices.Attacks.Bkw.bkw_end_to_end
