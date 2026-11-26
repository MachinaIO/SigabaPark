import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyUnfolding
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2IndepUniqueness


set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Wall1

/-- Second factorial moment and Markov bounds for the hit event of a count. -/
theorem count_hit_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Ω → ℕ) (hM : Measurable M) (m : ℝ)
    (h₁ : Integrable (fun x ↦ (M x : ℝ)) μ)
    (h₂ : Integrable (fun x ↦ (M x : ℝ) * (M x - 1 : ℝ)) μ)
    (mean : ∫ x, (M x : ℝ) ∂μ = m)
    (fac : ∫ x, (M x : ℝ) * (M x - 1 : ℝ) ∂μ ≤ m ^ 2) :
    m / (1 + m) ≤ μ.real {x | 0 < M x} ∧ μ.real {x | 0 < M x} ≤ m := by
  classical
  let s := {x | 0 < M x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hM
  let I := s.indicator (1 : Ω → ℝ)
  have hi : Integrable I μ := (integrable_const 1).indicator hs
  have ei : ∫ x, I x ∂μ = μ.real s := integral_indicator_one hs
  have hm : 0 ≤ m := mean ▸ integral_nonneg (fun x ↦ Nat.cast_nonneg (M x))
  have hp : 0 < 1 + m := by linarith
  have upper : ∀ x, I x ≤ (M x : ℝ) := by
    intro x
    by_cases h : 0 < M x
    · simpa [I, s, h] using (show (1 : ℝ) ≤ M x by exact_mod_cast h)
    · simp [I, s, h]
  refine ⟨(div_le_iff₀ hp).2 ?_, ei ▸ mean ▸ integral_mono hi h₁ upper⟩
  have pt (x : Ω) : (2 * (1 + m) - 1) * M x - (M x : ℝ) * (M x - 1 : ℝ) ≤
      (1 + m)^2 * I x := by
    by_cases h : 0 < M x
    · simp [I, s, h]
      nlinarith [sq_nonneg ((M x : ℝ) - (1 + m))]
    · have hz : M x = 0 := by omega
      simp [I, s, hz]
  have h := integral_mono ((h₁.const_mul _).sub h₂) (hi.const_mul _) pt
  simp only [Pi.sub_apply] at h
  rw [integral_sub (h₁.const_mul (2 * (1 + m) - 1)) h₂, integral_const_mul, integral_const_mul, mean, ei] at h
  change m ≤ μ.real s * (1 + m)
  apply (mul_le_mul_iff_of_pos_right hp).mp
  nlinarith

open SigabaNeo.Rogers

private def evalPrim {n : ℕ} (v : ContentFiber n 1) (g : SL n) : E n :=
  WithLp.toLp 2 (g • fun j ↦ (v.val.val j : ℝ))

private theorem measurable_evalPrim {n : ℕ} (v : ContentFiber n 1) :
    Measurable (evalPrim v) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec (fun j ↦ (v.val.val j : ℝ)))
  unfold Matrix.mulVec dotProduct
  fun_prop

/-- Count both signs of primitive vectors, with weight one half per vector. -/
def primitiveBallPairs {n : ℕ} (r : ℝ) (g : SL n) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∑' v : ContentFiber n 1, (Metric.ball (0 : E n) r).indicator
    (1 : E n → ℝ≥0∞) (evalPrim v g)

/-- On a Haar fundamental domain, the primitive sign-pair mean is t/(2 ζ(n)).
The zeta factor is expressed by its positive Dirichlet series. -/
theorem primitiveBallPairs_mean {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    (∫⁻ g in D, primitiveBallPairs r g ∂groupHaar n) / groupHaar n D =
      volume (Metric.ball (0 : E n) r) / (2 * ∑' k, dilationWeight n k) := by
  classical
  let B := Metric.ball (0 : E n) r
  let u := B.indicator (1 : E n → ℝ≥0∞)
  have hu : Measurable u := measurable_one.indicator measurableSet_ball
  obtain ⟨C, prim, mass⟩ := siegel_primitive_orbit_covolume n hn D hm hd hf
  have hc : C ≠ 0 := fun h ↦ hp (by simpa [h] using mass.symm)
  have hz : (∑' k, dilationWeight n k) ≠ 0 := fun h ↦ hp (by simpa [h] using mass.symm)
  have hC := (ENNReal.lt_top_of_mul_ne_top_left (mass ▸ hf) hz).ne
  have term (v : ContentFiber n 1) :
      Measurable (fun g : SL n ↦ u (evalPrim v g)) := hu.comp (measurable_evalPrim v)
  unfold primitiveBallPairs
  change (∫⁻ g in D, (2 : ℝ≥0∞)⁻¹ * ∑' v : ContentFiber n 1, u _ ∂_) / _ = _
  rw [lintegral_const_mul _ (Measurable.tsum term), lintegral_tsum
    (fun v ↦ (term v).aemeasurable)]
  change (2 : ℝ≥0∞)⁻¹ * (∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val) / _ = _
  rw [prim u hu, show (∫⁻ x, u x) = volume B by simp [u, B, lintegral_indicator measurableSet_ball],
    ← mass, ← mul_assoc, mul_comm _ C, mul_assoc, ENNReal.mul_div_mul_left _ _ hc hC]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, B, ENNReal.mul_inv]

/-- A primitive vector in the ball contributes its negative as a second signed hit. -/
theorem primitiveBallPairs_hit_upper {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    (groupHaar n).restrict D {g | 0 < primitiveBallPairs r g} / groupHaar n D ≤
      volume (Metric.ball (0 : E n) r) / (2 * ∑' k, dilationWeight n k) := by
  classical
  let B := Metric.ball (0 : E n) r
  let f (v : ContentFiber n 1) (g : SL n) := B.indicator (1 : E n → ℝ≥0∞) (evalPrim v g)
  have meas (v : ContentFiber n 1) : Measurable (f v) :=
    (measurable_one.indicator measurableSet_ball).comp (measurable_evalPrim v)
  rw [← primitiveBallPairs_mean hn D hm hd hp hf r]
  apply ENNReal.div_le_div_right
  apply meas_le_lintegral₀ ((measurable_const.mul (Measurable.tsum meas)).aemeasurable)
  intro g hg
  change 0 < (2 : ℝ≥0∞)⁻¹ * ∑' v, f v g at hg
  obtain ⟨v, hv⟩ : ∃ v, evalPrim v g ∈ B := by
    by_contra! h
    simp [f, Set.indicator_of_notMem, h] at hg
  let w : ContentFiber n 1 := ⟨⟨-v.val.val, neg_ne_zero.mpr v.val.property⟩, by
    simpa [vectorContent] using v.property⟩
  have ne : v ≠ w := by
    intro he
    apply v.val.property
    funext i
    have hi := congrArg (fun a : ContentFiber n 1 ↦ a.val.val i) he
    change v.val.val i = -(v.val.val i) at hi
    change v.val.val i = 0
    omega
  have ew : evalPrim w g = -evalPrim v g := by
    unfold evalPrim
    have e : (fun j ↦ (w.val.val j : ℝ)) = -(fun j ↦ (v.val.val j : ℝ)) := by
      funext j
      simp [w]
    rw [e, smul_neg]
    rfl
  have hw : evalPrim w g ∈ B := by simpa [B, ew, Metric.mem_ball, dist_zero_right] using hv
  have hsum := sum_le_tsum (f := fun a ↦ f a g) ({v, w} : Finset _)
  have ht : (2 : ℝ≥0∞) ≤ ∑' a, f a g := by
    simpa [ne, f, hv, hw, one_add_one_eq_two] using hsum
  change 1 ≤ (2 : ℝ≥0∞)⁻¹ * ∑' a, f a g
  calc
    1 = (2 : ℝ≥0∞)⁻¹ * 2 := (ENNReal.inv_mul_cancel (by norm_num) (by simp)).symm
    _ ≤ _ := mul_le_mul_right ht _

/-- The normalized intensity of unrestricted independent ordered pairs in the ball is t².
To obtain the factorial moment of primitive sign pairs one still needs the two-content
Möbius inversion and the identification with distinct ordered sign pairs. -/
theorem independentBallPairs_mean {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    independentPairMeasure D (Set.univ.pi (fun _ ↦ Metric.ball (0 : E n) r)) /
      groupHaar n D = volume (Metric.ball (0 : E n) r) ^ 2 := by
  obtain ⟨C, hC⟩ := independentPairMeasure_proportional hn hd hf
  rw [hC, independentPairMeasure_scalar_calibration hn hd hf hC,
    Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  rw [mul_comm (groupHaar n D), ENNReal.mul_div_cancel_right hp hf]
  simp

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.count_hit_bounds
#print axioms SigabaNeo.Wall1.primitiveBallPairs_mean
#print axioms SigabaNeo.Wall1.primitiveBallPairs_hit_upper
#print axioms SigabaNeo.Wall1.independentBallPairs_mean
