import Definitions.Def_LatticeAttack_Research_Wall1_TerminalMajorant506
import Definitions.Def_LatticeAttack_Research_Wall1_ComplexGaussianLattice

set_option autoImplicit true

/-! # Gaussian mass of the dual of a projected coordinate lattice

Restricting to a basis of projected coordinate axes supplies an injection into integer
coordinates in the intrinsic dimension. The discarded squared coordinates are nonnegative.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Submodule Module
open scoped RealInnerProductSpace

variable {N : ℕ}

/-- A coordinate minor of full intrinsic rank that separates all vectors of the subspace. -/
theorem exists_separating_coordinates (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ a : Fin (finrank ℝ S) ↪ Fin N, Function.Injective
      (fun x : S ↦ fun i ↦ (x.val : (EuclideanSpace ℝ (Fin N))) (a i)) := by
  classical
  let P := S.orthogonalProjectionOnto.toLinearMap
  let p (i : Fin N) := P ((EuclideanSpace.basisFun (Fin N) ℝ) i)
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ p
  let := Fintype.ofInjective a ha
  have htop : span ℝ (Set.range p) = ⊤ := by
    change span ℝ (Set.range (P ∘ (EuclideanSpace.basisFun (Fin N) ℝ))) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (show span ℝ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ)) = ⊤ by simpa using ((EuclideanSpace.basisFun (Fin N) ℝ)).toBasis.span_eq), Submodule.map_top]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x.val, S.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  let B := Basis.mk hli (hspan.trans htop).ge
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis B).symm
  refine ⟨⟨a ∘ e.symm, ha.comp e.symm.injective⟩, ?_⟩
  intro x y h
  have he : (innerₗ S) x = (innerₗ S) y := by
    apply B.ext
    intro i
    change ⟪x, B i⟫ = ⟪y, B i⟫
    simp only [B, Basis.mk_apply, Function.comp_apply, p, P,
      ContinuousLinearMap.coe_coe, S.inner_orthogonalProjectionOnto_eq_of_mem_left,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial]
    simpa [Function.comp_apply] using congrFun h (e i)
  exact ext_inner_right ℝ (fun z ↦ DFunLike.congr_fun he z)

private theorem integerGaussian_hasSum (d : ℕ) {a : ℝ} (ha : 0 < a) :
    HasSum (fun z : Fin d → ℤ ↦ Real.exp (-a * ∑ i, (z i : ℝ)^2))
      ((∑' k : ℤ, Real.exp (-a * (k : ℝ)^2))^d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hk := (summable_int_gauss ha).hasSum
    have hp := hk.mul ih (summable_mul_of_summable_norm hk.summable.norm ih.summable.norm)
    apply (Fin.snocEquiv (fun _ : Fin (d+1) ↦ ℤ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.sum_univ_castSucc, mul_add, Real.exp_add,
      pow_succ, mul_comm, add_comm] using hp

/-- The dual Gaussian bound for the full marked preimage P_S ℤ^N at every positive scale. -/
theorem projected_integer_dual_gaussian (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) {u : ℝ} (hu : 0 < u) :
    let K := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S
    Summable (fun x : metricDual K ↦ Real.exp (-Real.pi*u^2*‖x.val‖^2)) ∧
      (∑' x : metricDual K, Real.exp (-Real.pi*u^2*‖x.val‖^2)) ≤
        terminalTheta u ^ finrank ℝ S := by
  classical
  intro K
  obtain ⟨a, ha⟩ := exists_separating_coordinates S
  have hz (x : metricDual K) (i : Fin N) : ∃ z : ℤ, (z : ℝ) = ((x.val : S) : (EuclideanSpace ℝ (Fin N))) i := by
    have hi : S.orthogonalProjectionOnto ((EuclideanSpace.basisFun (Fin N) ℝ) i) ∈ K :=
      ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (x.property _ hi)
    refine ⟨z, ?_⟩
    simpa [EuclideanSpace.inner_single_right, EuclideanSpace.basisFun_apply] using hz
  let f (x : metricDual K) (j : Fin (finrank ℝ S)) := (hz x (a j)).choose
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply ha
    funext j
    exact (hz x _).choose_spec.symm.trans
      ((congrArg (fun t : ℤ ↦ (t : ℝ)) (congrFun h j)).trans (hz y _).choose_spec)
  let b := Real.pi*u^2
  have hb : 0 < b := by dsimp [b]; positivity
  let G (z : Fin (finrank ℝ S) → ℤ) := Real.exp (-b * ∑ i, (z i : ℝ)^2)
  have hG := integerGaussian_hasSum (finrank ℝ S) hb
  have hh (x : metricDual K) : Real.exp (-Real.pi*u^2*‖x.val‖^2) ≤ G (f x) := by
    have hc : ∑ j, ((f x j : ℤ) : ℝ)^2 ≤ ‖x.val‖^2 := by
      change _ ≤ ‖(x.val.val : (EuclideanSpace ℝ (Fin N)))‖^2
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [f, (hz _ _).choose_spec]
      rw [← Finset.sum_map Finset.univ a (fun j ↦ ((x.val.val : (EuclideanSpace ℝ (Fin N))) j)^2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
    apply Real.exp_le_exp.mpr
    simpa [G, b, neg_mul] using (mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hb.le))
  have hs : Summable (fun x : metricDual K ↦ Real.exp (-Real.pi*u^2*‖x.val‖^2)) :=
    Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) hh (hG.summable.comp_injective hf)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' z, G z := hs.tsum_le_tsum_of_inj f hf (fun _ _ ↦ (Real.exp_pos _).le) hh hG.summable
    _ = _ := hG.tsum_eq
    _ ≤ _ := pow_le_pow_left₀ (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
      (by simpa [b, neg_mul] using integerGaussian_le_terminalTheta hu) _


/-- The Part 161 frequency bound on a full-rank, discrete projection of the integer grid. -/
theorem projected_complex_gaussian (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (z τ : ℝ) (hz : 0 < z)
    [DiscreteTopology (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)]
    [IsZLattice ℝ (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S)] :
    let K := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))) S
    let d := finrank ℝ S
    let b : ℂ := ((Real.pi / z^2 : ℝ) : ℂ) * ⟨1, τ⟩
    ‖∑' x : K, Complex.exp (-b * ‖x.val‖^2)‖ ≤
      z^d / ZLattice.covolume K * (1+τ^2)^(-(d:ℝ)/4) *
        terminalTheta (z/Real.sqrt (1+τ^2))^d := by
  intro K d b
  let t := 1+τ^2
  have ht : 0 < t := by dsimp [t]; positivity
  have hp := Real.pi_pos
  have hb : 0 < b.re := by
    simpa only [b, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_one, zero_mul, sub_zero]
      using div_pos hp (sq_pos_of_pos hz)
  have hn : ‖b‖ = Real.pi/z^2 * Real.sqrt t := by
    rw [show b = _ from (rfl : b = ((Real.pi/z^2 : ℝ) : ℂ) * ⟨1, τ⟩), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Complex.norm_def]
    simp [Complex.normSq_apply, t, sq]
  have he : ((Real.pi : ℂ)^2 / b).re = Real.pi * (z / Real.sqrt t)^2 := by
    rw [Complex.div_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_div, add_zero, Complex.normSq_eq_norm_sq, hn, mul_pow, div_pow,
      Real.sq_sqrt ht.le]
    simp only [b, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_one, zero_mul,
      sub_zero]
    rw [div_pow, Real.sq_sqrt ht.le]
    field_simp
  have hfactor : (Real.pi / ‖b‖) ^ ((d:ℝ)/2) = z^d * t^(-(d:ℝ)/4) := by
    rw [hn, show Real.pi / (Real.pi/z^2*Real.sqrt t) = z^2 / Real.sqrt t by field_simp,
      Real.div_rpow (sq_nonneg _) (Real.sqrt_nonneg _) _, ← Real.rpow_natCast z 2,
      ← Real.rpow_mul hz.le, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le,
      show ((2:ℕ):ℝ) * (d/2 : ℝ) = d by ring, Real.rpow_natCast,
      show -(d:ℝ)/4 = -(1/2 * (d/2 : ℝ)) by ring, Real.rpow_neg ht.le, div_eq_mul_inv]
  have h := complex_gaussian_poisson_bound K hb
  rw [he] at h
  change _ ≤ (Real.pi / ‖b‖)^((d:ℝ)/2) / _ * _ at h
  rw [hfactor] at h
  have hd := (projected_integer_dual_gaussian S (div_pos hz (Real.sqrt_pos.mpr ht))).2
  have hc := ZLattice.covolume_pos K MeasureTheory.volume
  calc
    _ ≤ _ := h
    _ ≤ (z^d * t^(-(d:ℝ)/4) / ZLattice.covolume K) * terminalTheta (z/Real.sqrt t)^d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [neg_mul] using hd
    _ = _ := by dsimp only [t]; ring

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.exists_separating_coordinates
#print axioms SigabaNeo.Wall1.TerminalProjection.projected_integer_dual_gaussian

#print axioms SigabaNeo.Wall1.TerminalProjection.projected_complex_gaussian
