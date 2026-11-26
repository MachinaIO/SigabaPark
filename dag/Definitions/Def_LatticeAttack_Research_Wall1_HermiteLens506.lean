import Definitions.Def_LatticeAttack_Research_Wall1_HermiteWitness506

set_option autoImplicit true

/-! Signed lens integrals for the rank-506 spherical polynomial. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506

open Real MeasureTheory Metric Finset
open scoped RealInnerProductSpace Classical

/-- Normalized zonal polynomials of two consecutive degrees, evaluated at x. -/
def zonalPair (x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1,x)
  | j+1 =>
    let (a,b) := zonalPair x j
    let k : ℝ := j+1
    (b, ((2*k+504)*x*b-k*a)/(k+504))

def sphericalFactor (x : ℝ) : ℝ :=
  ∑ j ∈ range 32, (q j : ℝ) * (zonalPair x j).1

def sphericalKernel (x : ℝ) : ℝ := (x-(threshold:ℝ)) * sphericalFactor x ^ 2

private theorem zonal_cont (j : ℕ) : Continuous (fun x ↦ zonalPair x j) := by
  induction j with
  | zero => exact continuous_const.prodMk continuous_id
  | succ j ih =>
    change Continuous fun x : ℝ ↦ ((zonalPair x j).2, _)
    have ha := ih.fst
    have hb := ih.snd
    exact hb.prodMk (by fun_prop)

theorem kernel_continuous : Continuous sphericalKernel := by
  unfold sphericalKernel sphericalFactor
  have h (j : ℕ) := (zonal_cont j).fst
  fun_prop

/-- The proof uses squared minimum one. The kernel is zero off the actual open lens. -/
def lens {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (w x : E) : ℝ :=
  if ‖x‖ < R ∧ ‖x+w‖ < R then sphericalKernel (⟪x,x+w⟫ / (‖x‖*‖x+w‖)) else 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem corners {a b R t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haR : a ≤ R) (hbR : b ≤ R) (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    a^2+b^2-2*t*a*b ≤ 2*(1-t)*R^2 := by
  have ha2 := pow_le_pow_left₀ ha haR 2
  have hb2 := pow_le_pow_left₀ hb hbR 2
  have h : a^2+b^2-a*b ≤ R^2 := by
    rcases le_total a b with h | h
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr h)]
  nlinarith only [mul_nonneg (show 0 ≤ 1-2*t by linarith) (show 0 ≤ 2*R^2-(a^2+b^2) by linarith),
    mul_nonneg ht (sub_nonneg.mpr h)]

/-- Outside the enlargement shell the lens has a pointwise sign, before integration. -/
theorem lens_nonpos_of_separation {R : ℝ} {w : E}
    (hw : 2*(1-(threshold:ℝ))*R^2 ≤ ‖w‖^2) (x : E) : lens R w x ≤ 0 := by
  unfold lens
  split_ifs with h
  · apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply sub_nonpos.mpr
    have ht : 0 ≤ (threshold:ℝ) := by norm_num [threshold]
    by_cases hz : ‖x‖*‖x+w‖ = 0
    · simpa [hz] using ht
    apply (div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hz))).mpr
    have hh := corners (norm_nonneg x) (norm_nonneg (x+w)) h.1.le h.2.le ht
      (show (threshold:ℝ) ≤ 1/2 by norm_num [threshold])
    have he := norm_sub_sq_real x (x+w)
    rw [sub_add_cancel_left, norm_neg] at he
    linarith only [hh,hw,he]
  · exact le_rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lens_integrable (R : ℝ) (w : E) : Integrable (lens R w) := by
  let B := ball (0:E) R
  let F := fun x : E ↦ sphericalKernel (⟪x,x+w⟫ / (‖x‖*‖x+w‖))
  have hF : Measurable F := kernel_continuous.measurable.comp (by fun_prop)
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image
    (K := Set.Icc (-1:ℝ) 1) kernel_continuous.norm.continuousOn
  have bound (x : E) : ‖F x‖ ≤ C := by
    apply hC
    refine ⟨_,?_,rfl⟩
    rw [Set.mem_Icc,← abs_le,abs_div,abs_of_nonneg (by positivity : 0 ≤ ‖x‖*‖x+w‖)]
    by_cases hz : ‖x‖*‖x+w‖ = 0
    · simp [hz]
    exact (div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hz))).mpr (abs_real_inner_le_norm ..)
  let T := {x : E | ‖x‖ < R ∧ ‖x+w‖ < R}
  have hT : MeasurableSet T := (measurableSet_lt (f:=fun x : E ↦ ‖x‖) (by fun_prop) measurable_const).inter
    (measurableSet_lt (f:=fun x : E ↦ ‖x+w‖) (by fun_prop) measurable_const)
  have hsub : T ⊆ B := fun x h ↦ mem_ball_zero_iff.mpr h.1
  have he : lens R w = T.indicator F := by
    funext x
    by_cases h : x ∈ T
    · rw [Set.indicator_of_mem h]; exact ite_eq_left h
    · rw [Set.indicator_of_notMem h]; exact ite_eq_right h
  rw [he,integrable_indicator_iff hT]
  exact IntegrableOn.of_bound ((measure_mono hsub).trans_lt measure_ball_lt_top)
    hF.aestronglyMeasurable C (ae_of_all _ bound)

/-- A fixed relative displacement unfolds to a single signed Euclidean lens integral. -/
theorem unfold_lens (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {A : Set E} (hA : IsAddFundamentalDomain L.toAddSubgroup A volume)
    (R : ℝ) (w : E) :
    (∑' v : L.toAddSubgroup, ∫ x in A, lens R w (v.val+x)) = ∫ x, lens R w x := by
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  exact (hA.integral_eq_tsum'' _ (lens_integrable R w)).symm

/-- At fixed minimum s, only separations in the thin open upper shell require
the signed radial integral. The far and empty lenses are covered as well. -/
theorem lens_sum_nonpos {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    {A : Set E} (hA : IsAddFundamentalDomain L.toAddSubgroup A volume)
    {s R : ℝ} (hmin : ∀ w : L, w ≠ 0 → s ≤ ‖(w:E)‖)
    (near : ∀ w : L, w ≠ 0 → s ≤ ‖(w:E)‖ → ‖(w:E)‖^2 < 2*(1-(threshold:ℝ))*R^2 →
      (∫ x, lens R (w:E) x) ≤ 0) (D : Finset L) (hD : (0:L) ∉ D) :
    (∑ w ∈ D, ∑' v : L.toAddSubgroup, ∫ x in A, lens R (w:E) (v.val+x)) ≤ 0 := by
  apply sum_nonpos
  intro w hw
  rw [unfold_lens _ hA]
  have hn : w ≠ 0 := fun he ↦ hD (he ▸ hw)
  by_cases hfar : 2*(1-(threshold:ℝ))*R^2 ≤ ‖(w:E)‖^2
  · exact integral_nonpos (lens_nonpos_of_separation hfar)
  · exact near w hn (hmin w hn) (lt_of_not_ge hfar)

end SigabaNeo.Wall1.HermiteWitness506

#print axioms SigabaNeo.Wall1.HermiteWitness506.lens_integrable
#print axioms SigabaNeo.Wall1.HermiteWitness506.unfold_lens
#print axioms SigabaNeo.Wall1.HermiteWitness506.lens_sum_nonpos
