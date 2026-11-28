import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedDualCoordinates
import Definitions.Def_LatticeAttack_Research_Wall1_RadialCountingBins
import CslibFrontier.Foundations.Probability.Gaussian.Discrete

set_option autoImplicit true

/-! # Radial counting for a projected integer grid of intrinsic rank 506

A finite subset of the physical ball disjoint from its negative costs at most half the
full radial majorant. The determinant in the result is that of the projected grid.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Module Real MeasureTheory Submodule

variable {N : ℕ}

theorem projected_ball_count (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hd : finrank ℝ S = 506)
    (R : ℝ) (hR : 0 < R) [DiscreteTopology (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)]
    [IsZLattice ℝ (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)]
    (A : Finset (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S))
    (hA : ∀ x ∈ A, ‖x.val‖ ≤ R) (hneg : ∀ x ∈ A, -x ∉ A) :
    (A.card : ℝ) ≤ countingConstantAt (R * sqrt (2*π/506)) *
      terminalBallVolume * R^506 / ZLattice.covolume (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S) := by
  classical
  let K := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S
  let z := R * sqrt (2*π/506)
  have hz : 0 < z := by dsimp [z]; positivity
  let X (x : K) := 253 - π * ‖x.val‖^2 / z^2
  let mass (x : K) := exp (X x)
  have hs : Summable mass := by
    have h := ZLattice.summable_gaussianWeight K z hz 0
    apply (h.mul_left (exp 253)).congr
    intro x
    simp only [mass, X, ProbabilityTheory.gaussianWeight, sub_zero, Real.exp_sub,
      div_eq_mul_inv, Real.exp_neg, neg_mul]
  let B : Finset K := A ∪ A.map (Equiv.neg K).toEmbedding
  have hb : ∀ x ∈ B, ‖x.val‖ ≤ R := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hA _ h
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
      simpa using hA y hy
  have hcard : (B.card : ℝ) = 2*A.card := by
    have hdis : Disjoint A (A.map (Equiv.neg K).toEmbedding) := by
      apply Finset.disjoint_left.mpr
      intro x hx h
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
      exact hneg y hy hx
    simp [B, Finset.card_union_of_disjoint hdis, two_mul]
  have hzsq : z^2 = R^2*(2*π/506) := by
    dsimp only [z]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hX (x : K) (h : x ∈ B) : 0 ≤ X x ∧ 2 * X x < 507 := by
    constructor
    · apply sub_nonneg.mpr
      apply (div_le_iff₀ (by positivity)).mpr
      rw [hzsq]
      calc
        _ ≤ π * R^2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hb x h) 2) pi_pos.le
        _ = _ := by ring
    · dsimp only [X]
      have : 0 ≤ π * ‖x.val‖^2 / z^2 := by positivity
      linarith
  let χ (t : ℝ) := ∑' x : K, (mass x : ℂ)*Complex.exp ((t*X x : ℝ)*Complex.I)
  let k := exp 253 * (z^506 / ZLattice.covolume K)
  have hv := ZLattice.covolume_pos K volume
  have hk : 0 < k := by dsimp [k]; positivity
  have hχ : Continuous χ := by
    apply continuous_tsum (fun _ ↦ by fun_prop) hs
    intro x t
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mass, abs_of_pos (exp_pos _),
      Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have freq (t : ℝ) : ‖χ t‖ ≤ k *
      ((1+t^2)^(-(506/4):ℝ) * terminalTheta (z/sqrt (1+t^2))^506) := by
    let b : ℂ := ((π/z^2:ℝ):ℂ) * ⟨1,t⟩
    let p : ℂ := (exp 253 : ℝ) * Complex.exp ((t*253:ℝ)*Complex.I)
    have hphase : ‖p‖ = exp 253 := by
      simp only [p, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have eq (x : K) : (mass x : ℂ)*Complex.exp ((t*X x : ℝ)*Complex.I) =
        p*Complex.exp (-b*‖x.val‖^2) := by
      simp only [p, mass, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp only [X,b]
      rw [show (⟨1,t⟩ : ℂ) = 1 + (t:ℂ)*Complex.I by apply Complex.ext <;> simp]
      push_cast
      ring
    change ‖∑' x : K, (mass x : ℂ)*_‖ ≤ _
    simp_rw [eq, tsum_mul_left, norm_mul, hphase]
    have h := projected_complex_gaussian S z t hz
    dsimp only at h
    rw [hd] at h
    norm_num only [Nat.cast_ofNat] at h
    exact (mul_le_mul_of_nonneg_left h (exp_pos _).le).trans_eq (by dsimp only [k,K]; ring)
  let F (t : ℝ) := (1-t/8)*‖χ t‖ / k
  have Fcont : Continuous F := ((continuous_const.sub (continuous_id.div_const 8)).mul
    hχ.norm).div_const k
  have hF := frequency_integral_le_bins hz F Fcont (by
    intro t ht
    apply (div_le_iff₀ hk).mpr
    have h := mul_le_mul_of_nonneg_left (freq t) (by linarith [ht.2] : 0 ≤ 1-t/8)
    linarith only [h])
  have hc := count_le_frequency_integral X B hs (n := 507) hX
  change _ ≤ _ * ∫ t in (0:ℝ)..8, (1-t/8)*‖χ t‖ at hc
  rw [hcard] at hc
  have hi : (∫ t in (0:ℝ)..8, (1-t/8)*‖χ t‖) ≤
      k * ∑ j ∈ Finset.range 4096,
        (1/512)*(1-(j:ℝ)/512/8)*(1+((j:ℝ)/512)^2)^(-(506/4):ℝ)*
          terminalTheta (z/sqrt (1+(((j:ℝ)+1)/512)^2))^506 := by
    dsimp only [F] at hF
    rw [intervalIntegral.integral_div] at hF
    simpa only [mul_comm k] using (div_le_iff₀ hk).mp hF
  have hden : 0 < 1-exp (-(1/2)) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have ht := hc.trans (mul_le_mul_of_nonneg_left hi (by positivity))
  have hsin : 0 < Real.sin 1 := sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [pi_gt_three])
  have hV : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  have hp : z^506 = R^506*(2*π/506)^253 := by
    rw [show (506:ℕ) = 2*253 by decide, pow_mul, hzsq, mul_pow, pow_mul]
  apply (le_div_iff₀ hv).mpr
  change _ ≤ countingConstantAt z * _ * _
  unfold countingConstantAt
  dsimp only
  dsimp only [k] at ht
  rw [hp] at ht
  field_simp [hV.ne', hsin.ne', hden.ne', hv.ne'] at ht ⊢
  linarith only [ht]


/-- The candidate-to-mark ratio in the existing window API, given a physical coordinate
realization of the appended preimage inside a projected grid and its determinant normalization. -/
theorem projected_candidates_count {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (M K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K]
    [Fintype (Marks M K)] (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hd : finrank ℝ S = 506)
    [DiscreteTopology (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)]
    [IsZLattice ℝ (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)]
    (e : WindowSpace V →ₗᵢ[ℝ] S)
    (he : ∀ x ∈ appendWindow K 0, e x ∈ projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)
    {D : ℝ} (hD : D = Fintype.card (Marks M K) *
      ZLattice.covolume (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S))
    (R : ℝ) (hR : 0 < R) :
    (candidates K R).card / (Fintype.card (Marks M K) : ℝ) ≤
      countingConstantAt (R * sqrt (2*π/506)) * (R/terminalScale D)^506 := by
  classical
  let L := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S
  let T := candidates K R
  let f : T ↪ L := ⟨fun x ↦ ⟨e x.val, he _ (mem_candidates.mp x.property).1⟩,
    fun x y h ↦ Subtype.ext (e.injective (congrArg Subtype.val h))⟩
  let A := T.attach.map f
  have bound : ∀ x ∈ A, ‖x.val‖ ≤ R := by
    intro x hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hx
    change ‖e w.val‖ ≤ R
    rw [e.norm_map]
    exact (mem_candidates.mp w.property).2.2
  have sign : ∀ x ∈ A, -x ∉ A := by
    intro x hx hn
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, _, hw⟩ := Finset.mem_map.mp hn
    have heq : e w.val = -e v.val := congrArg Subtype.val hw
    rw [← map_neg] at heq
    have h := congrArg WithLp.snd (e.injective heq)
    have hv := (mem_candidates.mp v.property).2.1
    have hw' := (mem_candidates.mp w.property).2.1
    change w.val.snd = -v.val.snd at h
    linarith
  let C := countingConstantAt (R * sqrt (2*π/506))
  have ha := projected_ball_count S hd R hR A bound sign
  change (A.card : ℝ) ≤ C * terminalBallVolume * R^506 / ZLattice.covolume L at ha
  rw [show A.card = T.card by simp [A]] at ha
  have hv := ZLattice.covolume_pos L volume
  have hcard : 0 < (Fintype.card (Marks M K) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hvol : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  have hD' : 0 < D := hD ▸ mul_pos hcard hv
  have hscale : (terminalScale D)^506 = D/terminalBallVolume := by
    unfold terminalScale
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (n := 506) (by positivity) (by decide)
  change (T.card : ℝ) / _ ≤ C * (R/terminalScale D)^506
  rw [div_pow, hscale, hD]
  calc
    _ ≤ (C * terminalBallVolume * R^506 / ZLattice.covolume L) / Fintype.card (Marks M K) :=
      div_le_div_of_nonneg_right ha hcard.le
    _ = _ := by dsimp only [L]; field_simp

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.projected_ball_count

#print axioms SigabaNeo.Wall1.TerminalProjection.projected_candidates_count
