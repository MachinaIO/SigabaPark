import Definitions.Def_LatticeAttack_Research_Wall1_ControlledDrawLaw
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit true

/-! Positive-height Gaussian counting for every forced old state. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 Module Submodule Real MeasureTheory
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem height_gaussian {z : ℝ} (hz : 0 < z) :
    let f := fun x : ℝ ↦ exp (-(π/z^2)*x^2)
    Summable (fun j : ℕ ↦ f (j+1 : ℕ)) ∧ (∑' j : ℕ, f (j+1 : ℕ)) ≤ z/2 := by
  intro f
  have ha : 0 < π/z^2 := by positivity
  have anti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y _ hxy
    exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx hxy 2) (neg_nonpos.mpr ha.le))
  have hi : IntegrableOn f (Set.Ioi 0) := (integrable_exp_neg_mul_sq ha).integrableOn
  have hn : ∀ x ∈ Set.Ioi 0, 0 ≤ f x := fun _ _ ↦ (exp_pos _).le
  refine ⟨(anti.summable_of_integrableOn_Ioi_zero hi hn).comp_injective Nat.succ_injective, ?_⟩
  apply (anti.tsum_add_one_le_integral hi hn).trans_eq
  dsimp only [f]
  rw [integral_gaussian_Ioi, div_div_eq_mul_div, mul_div_cancel_left₀ _ pi_pos.ne',
    sqrt_sq hz.le]

private theorem projected_mass {n : ℕ} (S : Submodule ℝ (CoordSpace n))
    [DiscreteTopology (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))) S)]
    [IsZLattice ℝ (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))) S)]
    {z : ℝ} (hz : 0 < z) :
    let G := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))) S
    (∑' x : G, exp (-(π/z^2)*‖x.val‖^2)) ≤
      z^(finrank ℝ S) / ZLattice.covolume G * terminalTheta z ^ finrank ℝ S := by
  intro G
  have h := projected_complex_gaussian S z 0 hz
  have ei : (⟨1, 0⟩ : ℂ) = 1 := rfl
  simp only [ei, mul_one, zero_pow (by decide : 2 ≠ 0), add_zero, one_rpow, sqrt_one,
    div_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- At any positive width the Gaussian on the old projected grid times the
positive-height Gaussian majorizes every point in the physical candidate ball. -/
theorem candidateRatio_gaussian {n d : ℕ} (s : ChainState n (CoordSpace d))
    {r z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    candidateRatio s r ≤ exp (π*r^2/z^2) / 2 * z^(d+1) * terminalTheta z^d /
      ZLattice.covolume s.M := by
  let K := markedPreimage s.M s.g
  have sub : s.M ≤ K := by dsimp [K]; rw [markedPreimage_eq]; exact le_sup_left
  let : DiscreteTopology K := markedPreimage_discrete _ _ _ s.periods (by decide)
  let : IsZLattice ℝ K := ⟨top_unique <| (IsZLattice.span_top (K := ℝ) (L := s.M)).ge.trans
    (span_mono sub)⟩
  let := Finite.of_surjective _ (columnMark_surjective s.M s.g s.periods)
  letI : Fintype (Marks s.M K) := Fintype.ofFinite _
  let S := s.frame.space
  let G := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))) S
  have he : G = transport s.frame.embed K := by
    dsimp only [G,S,K]
    rw [transport_eq, AxisFrame.grid_eq, s.marked]
  let : DiscreteTopology G := he ▸ inferInstanceAs (DiscreteTopology (transport _ K))
  let : IsZLattice ℝ G := ⟨by rw [he]; exact IsZLattice.span_top⟩
  have hd : finrank ℝ S = d := by rw [← s.frame.embed.toLinearEquiv.finrank_eq]; simp
  have det : (Fintype.card (Marks s.M K) : ℝ) * ZLattice.covolume G = ZLattice.covolume s.M := by
    rw [he, transport_covolume, marks_mul_covolume _ _ sub]
  let T := candidates K r
  have spec (w : T) := mem_candidates.mp w.property
  have lift (w : T) : ∃ j : ℕ, w.val.snd = (j+1 : ℕ) := by
    obtain ⟨k,hk⟩ := integral_height (spec w).1
    have hp : 0 < (k:ℝ) := hk ▸ (spec w).2.1
    have : 0 < k := by exact_mod_cast hp
    exact ⟨k.toNat-1, hk.trans (by exact_mod_cast (show k = ↑(k.toNat-1+1) by omega))⟩
  let j (w : T) := (lift w).choose
  have hj (w : T) : w.val.snd = (j w+1 : ℕ) := (lift w).choose_spec
  let x (w : T) : G := ⟨s.frame.embed w.val.fst, by
    rw [he, transport_eq]
    refine ⟨w.val.fst, (Quotient.mk_eq_zero K).mp ?_, rfl⟩
    have hm := (mem_append_at_height K 0 w.val (j w+1 : ℕ) (by exact_mod_cast hj w)).1 (spec w).1
    simpa using hm⟩
  let f (w : T) := (x w, j w)
  have inj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (s.frame.embed.injective (congrArg (fun p : G × ℕ ↦ p.1.val) h))
      ((hj v).trans ((congrArg (fun p : G × ℕ ↦ ((p.2+1 : ℕ):ℝ)) h).trans (hj w).symm))
  let a := π/z^2
  let P (x : G) := exp (-a*‖x.val‖^2)
  let H (j : ℕ) := exp (-a*((j+1 : ℕ):ℝ)^2)
  have hP : Summable P := (ZLattice.summable_gaussianWeight G z hz 0).congr (fun x ↦ by
    simp only [ProbabilityTheory.gaussianWeight, sub_zero, P, a]; congr 1; ring)
  obtain ⟨hH, hh⟩ := height_gaussian hz
  have prod := hP.hasSum.mul hH.hasSum
    (summable_mul_of_summable_norm hP.norm hH.norm)
  let C := exp (π*r^2/z^2)
  have wt (w : T) : 1 ≤ C * (P (x w) * H (j w)) := by
    simp only [C, P, H, ← exp_add, one_le_exp_iff, x, LinearIsometryEquiv.norm_map, ← hj]
    have hn := pow_le_pow_left₀ (norm_nonneg _) (spec w).2.2 2
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] at hn
    dsimp only [a]
    nlinarith [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ π/z^2),
      show π*r^2/z^2 = π/z^2*r^2 by ring]
  have bound := (hasSum_fintype (fun _ : T ↦ (1:ℝ))).summable.tsum_le_tsum_of_inj
    f inj (fun _ _ ↦ by positivity : ∀ p ∉ Set.range f, 0 ≤ C * (P p.1 * H p.2)) wt
    (prod.summable.mul_left C)
  have pm := projected_mass S hz
  rw [hd] at pm
  change (∑' x, P x) ≤ z^d / ZLattice.covolume G * terminalTheta z^d at pm
  change (∑' j, H j) ≤ _ at hh
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_coe, tsum_mul_left, prod.tsum_eq] at bound
  have hc := ZLattice.covolume_pos G volume
  have hc' : 0 < (Fintype.card (Marks s.M K) : ℝ) := by exact_mod_cast Fintype.card_pos
  have both := mul_le_mul pm hh (tsum_nonneg fun _ ↦ (exp_pos _).le)
    ((tsum_nonneg fun _ ↦ (exp_pos _).le).trans pm)
  change (T.card : ℝ) / _ ≤ _
  apply (div_le_iff₀ hc').mpr
  apply (bound.trans (mul_le_mul_of_nonneg_left both (exp_pos _).le)).trans_eq
  rw [← det, pow_succ z d]
  dsimp only [C]
  field_simp

private theorem plane_pos : 0 < planeRadius := by unfold planeRadius areaCut; positivity

private theorem cap_pos (k : ℕ) : 0 < flagCap k := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact ih.trans_le (le_max_left ..)

/-- The determinant guard alone suffices for the forced-state candidate estimate.
The state can be any physical state of the required dimension. -/
theorem flag_candidate_bound (u : FlagIndex) {n : ℕ}
    (s : ChainState n (CoordSpace (505-u.2.val)))
    (h : exp (flagFloor u) ≤ ZLattice.covolume s.M) :
    candidateRatio s (flagRadius u) ≤ flagCharge u := by
  let k := 155-u.1.val
  let j := u.2.val
  let p := 505-j
  let w := flagCap (k-j)
  let z := max 1 (w * sqrt (2*π/(p+1:ℝ)))
  have ht := plane_pos
  have hw : 0 < w := cap_pos _
  have hz : 0 < z := zero_lt_one.trans_le (le_max_left ..)
  have hc := candidateRatio_gaussian s (mul_pos ht hw).le (mul_pos ht hz)
  change candidateRatio s (flagRadius u) ≤
    exp (π*(planeRadius*w)^2/(planeRadius*z)^2) / 2 * (planeRadius*z)^(p+1) *
      terminalTheta (planeRadius*z)^p / ZLattice.covolume s.M at hc
  have e : π*(planeRadius*w)^2/(planeRadius*z)^2 = π*w^2/z^2 := by field_simp
  rw [e] at hc
  have hθ : 0 ≤ terminalTheta (planeRadius*z) := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans
    (integerGaussian_le_terminalTheta (mul_pos ht hz))
  apply hc.trans
  apply (div_le_div_of_nonneg_left (by positivity) (exp_pos _) h).trans_eq
  change _ = planeRadius^506 / 2 * exp (π*w^2/z^2-terminalLogFloor u.1.val +
    logCaps k-logCaps (k-j)) * z^(p+1) * terminalTheta (planeRadius*z)^p
  change _ / exp (terminalLogFloor u.1.val-logCaps k+logCaps (k-j)-j*log planeRadius) = _
  rw [exp_sub, exp_nat_mul, exp_log ht, mul_pow, exp_sub, exp_add, exp_sub, exp_add, exp_sub]
  have hj : p+1+j = 506 := by dsimp [p,j]; omega
  rw [← hj, pow_add planeRadius]
  field_simp
  <;> ring

/-- Only the maximum physical test radius is needed to apply the uniform-column
law once the deterministic candidate estimate is in place. -/
theorem flag_probability (u : FlagIndex) (hr : flagRadius u < 3329) :
    DualExit.probability (fun A ↦ flagTest flagRadius flagFloor u (history A)) ≤ flagCharge u := by
  apply flag_probability_of_count u hr
  · unfold flagCharge
    dsimp only
    have ht := plane_pos
    have hz : 0 < max 1 (flagCap (155-u.1.val-u.2.val)*sqrt (2*π/((505-u.2.val:ℕ)+1:ℝ))) :=
      zero_lt_one.trans_le (le_max_left ..)
    have hθ := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans
      (integerGaussian_le_terminalTheta (mul_pos ht hz))
    positivity
  · intro h
    exact flag_candidate_bound u _

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.candidateRatio_gaussian
#print axioms SigabaNeo.Wall1.ControlledPlane.flag_candidate_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.flag_probability
