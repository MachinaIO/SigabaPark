import Definitions.Def_LatticeAttack_Research_Wall1_SelectionLaw

set_option autoImplicit true

/-! Part 105. All projected lengths below are in the physical metric before determinant
normalization. The strict second-minimum event is expressed by independent witnesses. -/

noncomputable section
open MeasureTheory Submodule SigabaNeo.Rogers
open scoped ENNReal InnerProductSpace
namespace SigabaNeo.Wall1

/-- Integer coordinates in the lattice represented by a special linear matrix. -/
def latticePoint {n : ℕ} (g : SL n) : (Fin n → ℤ) →+ E n where
  toFun z := WithLp.toLp 2 (g • fun j ↦ (z j : ℝ))
  map_zero' := by
    change WithLp.toLp 2 (g.val.mulVec (fun j ↦ ((0 : Fin n → ℤ) j : ℝ))) = 0
    simp only [Pi.zero_apply, Int.cast_zero]
    exact congrArg (WithLp.toLp 2) (Matrix.mulVec_zero _)
  map_add' x y := by
    change WithLp.toLp 2 (g • _) = _
    simp only [Pi.add_apply, Int.cast_add]
    rw [show (fun j ↦ (x j : ℝ) + y j) = (fun j ↦ (x j : ℝ)) + (fun j ↦ (y j : ℝ)) from rfl,
      smul_add]
    rfl

/-- Strict second-minimum event. -/
def secondMinimumBelow {n : ℕ} (r : ℝ) : Set (SL n) :=
  {g | ∃ p : orderTwoIndependent n, ∀ i, ‖latticePoint g (p.val i).val‖ < r}

private abbrev Sym := Equiv.Perm (Fin 2) × (Fin 2 → Bool)

private def sign (b : Bool) : ℤˣ := if b then -1 else 1

private def signedPairs {n : ℕ} (p : orderTwoIndependent n) : Sym ↪ orderTwoIndependent n := by
  let z := fun i ↦ (p.val i).val
  have li : LinearIndependent ℤ z := p.property
  let f (a : Sym) (i : Fin 2) := (sign (a.2 i) : ℤ) • z (a.1 i)
  have h (a : Sym) : LinearIndependent ℤ (f a) :=
    (li.comp a.1 a.1.injective).units_smul _
  refine ⟨fun a ↦ ⟨fun i ↦ ⟨f a i, (h a).ne_zero i⟩, h a⟩, ?_⟩
  rintro ⟨s,b⟩ ⟨t,c⟩ he
  have eqn (i : Fin 2) := congrArg (fun q : orderTwoIndependent n ↦ (q.val i).val) he
  change ∀ i, (sign (b i) : ℤ) • z (s i) = (sign (c i) : ℤ) • z (t i) at eqn
  have st : s = t := Equiv.ext fun i ↦
    li.eq_of_smul_apply_eq_smul_apply _ _ _ _ (Units.ne_zero _) (eqn i)
  subst t
  congr 1
  funext i
  have e := li.smul_left_injective (s i) (eqn i)
  cases hb : b i <;> cases hc : c i <;> simp_all [sign]

/-- The eight signed orderings of an independent pair give the denominator eight. -/
theorem haar_secondMinimum_upper {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    (groupHaar n).restrict D (secondMinimumBelow r) / groupHaar n D ≤
      volume (Metric.ball (0 : E n) r) ^ 2 / 8 := by
  classical
  let B := Set.univ.pi (fun _ : Fin 2 ↦ Metric.ball (0 : E n) r)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_ball
  let F := B.indicator (1 : (Fin 2 → E n) → ℝ≥0∞)
  let f (p : orderTwoIndependent n) (g : SL n) := F (fun i ↦ latticePoint g (p.val i).val)
  have hm (p : orderTwoIndependent n) : Measurable (f p) := by
    apply (measurable_one.indicator hB).comp
    apply Measurable.of_eval
    intro i
    let : BorelSpace (SL n) := ⟨rfl⟩
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous (fun g : SL n ↦ g.val.mulVec _)
    unfold Matrix.mulVec dotProduct
    fun_prop
  have mean := independentPairMeasure_lintegral D F (measurable_one.indicator hB)
  rw [show ∫⁻ x, F x ∂independentPairMeasure D = independentPairMeasure D B by
    simp [F, lintegral_indicator hB]] at mean
  change independentPairMeasure D B = ∑' p, ∫⁻ g in D, f p g ∂groupHaar n at mean
  rw [← lintegral_tsum (fun p ↦ (hm p).aemeasurable)] at mean
  rw [← independentBallPairs_mean hn D hd hp hf r, ← mean.symm]
  conv_rhs => rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, ← div_eq_mul_inv]
  apply ENNReal.div_le_div_right
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div
    (Measurable.tsum hm).aemeasurable (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by simp))
  rintro g ⟨p,hp'⟩
  have hit (a : Sym) : f (signedPairs p a) g = 1 := by
    apply Set.indicator_of_mem
    intro i _
    change ‖latticePoint g ((sign (a.2 i) : ℤ) • (p.val (a.1 i)).val) - 0‖ < r
    cases hb : a.2 i <;> simpa [sign, hb] using hp' (a.1 i)
  have H := sum_le_tsum (f := fun q ↦ f q g) (Finset.univ.map (signedPairs p))
  simpa [Finset.sum_map, hit, Fintype.card_perm, Nat.factorial] using H

/-- Probability that the second minimum is at least the specified radius. -/
theorem haar_secondMinimum_lower {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    1 - volume (Metric.ball (0 : E n) r) ^ 2 / 8 ≤
      (groupHaar n).restrict D (secondMinimumBelow r)ᶜ / groupHaar n D := by
  let μ := (groupHaar n).restrict D
  let A : Set (SL n) := secondMinimumBelow r
  have h := measure_union_le (μ := μ) Aᶜ A
  rw [Set.compl_union_self, Measure.restrict_apply_univ] at h
  apply tsub_le_iff_right.mpr
  refine le_trans ?_ (add_le_add_right (haar_secondMinimum_upper hn D hd hp hf r) _)
  simp only [div_eq_mul_inv, ← add_mul]
  exact (ENNReal.div_self hp hf).symm.le.trans (ENNReal.div_le_div_right h _)

/-- A nearest lift keeps its perpendicular component and has small parallel component. -/
theorem roundedLift_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (v w : F) :
    ∃ k : ℤ, (ℝ ∙ v)ᗮ.starProjection (w - k • v) = (ℝ ∙ v)ᗮ.starProjection w ∧
      ‖w - k • v‖ ^ 2 ≤ ‖(ℝ ∙ v)ᗮ.starProjection w‖ ^ 2 + ‖v‖ ^ 2 / 4 := by
  let S := ℝ ∙ v
  obtain ⟨a, ha⟩ := mem_span_singleton.mp (S.starProjection_apply_mem w)
  let k := round (a : ℝ)
  have hperp : Sᗮ.starProjection (w - k • v) = Sᗮ.starProjection w := by
    simp only [map_sub, map_zsmul, S, starProjection_orthogonalComplement_singleton_eq_zero,
      zsmul_zero, sub_zero]
  refine ⟨k, hperp, ?_⟩
  have hfix : S.starProjection v = v := starProjection_eq_self_iff.mpr (mem_span_singleton_self v)
  have hs : S.starProjection (w - k • v) = (a - (k : ℝ)) • v := by
    simp only [map_sub, map_zsmul, hfix, ← ha, sub_smul, Int.cast_smul_eq_zsmul]
  have py := norm_sq_eq_add_norm_sq_starProjection (w - k • v) S
  rw [hperp, hs, norm_smul, Real.norm_eq_abs] at py
  have hr := mul_le_mul_of_nonneg_right (abs_sub_round a) (norm_nonneg v)
  change |a - (k : ℝ)| * ‖v‖ ≤ _ at hr
  change _ ≤ ‖Sᗮ.starProjection w‖ ^ 2 + _
  nlinarith [pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hr 2]

/-- A short rounded lift and a shortest vector witness the strict second minimum. -/
private theorem rounded_pair {n : ℕ} {g : SL n} {v u : Fin n → ℤ}
    (hv : latticePoint g v ≠ 0)
    (hu : (ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g u) ≠ 0)
    {r : ℝ} (hvlen : ‖latticePoint g v‖ < r) (hulen : ‖latticePoint g u‖ < r) :
    g ∈ secondMinimumBelow r := by
  let P := (ℝ ∙ latticePoint g v)ᗮ.starProjection
  have hPv : P (latticePoint g v) = 0 := starProjection_orthogonalComplement_singleton_eq_zero _
  have hv' : v ≠ 0 := fun e ↦ hv (by simp [e])
  have hu' : u ≠ 0 := fun e ↦ hu (by simp [e])
  have li : LinearIndependent ℤ ![v,u] := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have he := congrArg (fun z ↦ P (latticePoint g z)) h
    simp only [map_add, map_zsmul, hPv, zsmul_zero, zero_add, map_zero] at he
    rw [← Int.cast_smul_eq_zsmul ℝ] at he
    have hb : b = 0 := by exact_mod_cast (smul_eq_zero.mp he).resolve_right hu
    subst b
    simp only [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hv', rfl⟩
  let p : OrderTwoPair n := ![⟨v,hv'⟩, ⟨u,hu'⟩]
  refine ⟨⟨p, ?_⟩, ?_⟩
  · change LinearIndependent ℤ _
    convert li using 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    · exact hvlen
    · exact hulen

/-- Outside the strict second-minimum event every nonzero projection satisfies both the
length-sensitive squared bound and the uniform sqrt(3)/2 bound. -/
theorem quotientMinimum_gap {n : ℕ} {g : SL n} {v w : Fin n → ℤ}
    (hv : latticePoint g v ≠ 0)
    (hmin : ∀ z, latticePoint g z ≠ 0 → ‖latticePoint g v‖ ≤ ‖latticePoint g z‖)
    (hw : (ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g w) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (hsecond : g ∉ secondMinimumBelow r) :
    r ^ 2 - ‖latticePoint g v‖ ^ 2 / 4 ≤
      ‖(ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g w)‖ ^ 2 ∧
    Real.sqrt 3 / 2 * r ≤ ‖(ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g w)‖ := by
  let V := latticePoint g v
  let P := (ℝ ∙ V)ᗮ.starProjection
  obtain ⟨k, he, hb⟩ := roundedLift_sq V (latticePoint g w)
  let u := w - k • v
  have eu : latticePoint g u = latticePoint g w - k • V := by simp only [u,V,map_sub,map_zsmul]
  have hpu : P (latticePoint g u) ≠ 0 := by rwa [eu, he]
  have hmu := hmin u (fun e ↦ hpu (by rw [e,map_zero]))
  have hru : r ≤ ‖latticePoint g u‖ := by
    by_contra! h
    exact hsecond (rounded_pair hv hpu (hmu.trans_lt h) h)
  rw [← eu] at hb
  change r ^ 2 - ‖V‖ ^ 2 / 4 ≤ ‖P (latticePoint g w)‖ ^ 2 ∧ _
  change ‖latticePoint g u‖ ^ 2 ≤ ‖P (latticePoint g w)‖ ^ 2 + ‖V‖ ^ 2 / 4 at hb
  have hr2 := pow_le_pow_left₀ hr hru 2
  constructor
  · linarith
  · change _ ≤ ‖P (latticePoint g w)‖
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (norm_nonneg _)
    have hv2 := pow_le_pow_left₀ (norm_nonneg V) hmu 2
    nlinarith [congrArg (fun s : ℝ ↦ s * r ^ 2) (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))]

/-- The event allows every shortest-vector tie and needs no measurable tie-breaking rule. -/
theorem haar_quotientMinimum_upper {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
    (groupHaar n).restrict D {g | ∃ v w : Fin n → ℤ, latticePoint g v ≠ 0 ∧
      (∀ z, latticePoint g z ≠ 0 → ‖latticePoint g v‖ ≤ ‖latticePoint g z‖) ∧
      (ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g w) ≠ 0 ∧
      ‖(ℝ ∙ latticePoint g v)ᗮ.starProjection (latticePoint g w)‖ < c} / groupHaar n D ≤
      volume (Metric.ball (0 : E n) (2 * c / Real.sqrt 3)) ^ 2 / 8 := by
  refine le_trans (ENNReal.div_le_div_right (measure_mono ?_) _) (haar_secondMinimum_upper hn D hd hp hf _)
  rintro g ⟨v,w,hv,hm,hw,hs⟩
  by_contra h
  have he := (quotientMinimum_gap hv hm hw (r := 2*c/Real.sqrt 3) (by positivity) h).2
  have eqn : Real.sqrt 3 / 2 * (2*c/Real.sqrt 3) = c := by field_simp
  linarith

#print axioms haar_secondMinimum_upper
#print axioms haar_secondMinimum_lower
#print axioms roundedLift_sq
#print axioms quotientMinimum_gap
#print axioms haar_quotientMinimum_upper
end SigabaNeo.Wall1
