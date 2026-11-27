module

public import Definitions.Def_LatticeAttack_Research_Wall1_Ratio
import Mathlib.NumberTheory.Modular
import all Definitions.Def_LatticeAttack_Research_Wall1_Ratio
import all Definitions.Def_LatticeAttack_Reduction_Hermite2

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

/-- Modular reduction of a positive binary quadratic form of determinant D². -/
private theorem binary_short (A B C D : ℝ) (ha : 0 < A) (hd : 0 < D)
    (disc : A*C = B^2 + D^2) :
    ∃ c d : ℤ, (c ≠ 0 ∨ d ≠ 0) ∧
      Real.sqrt 3 * (C*c^2 + 2*B*c*d + A*d^2) ≤ 2*D := by
  let z : UpperHalfPlane := ⟨⟨B/A, D/A⟩, div_pos hd ha⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have ht := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
  have hh : Real.sqrt 3 ≤ 2*(g • z).im := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [ModularGroup.im_smul_eq_div_normSq] at hh
  have hn := UpperHalfPlane.normSq_denom_pos g z.im_ne_zero
  have h := (le_div_iff₀ hn).mp (show Real.sqrt 3 ≤ (2*z.im)/_ by
    rwa [mul_div_assoc])
  refine ⟨g 1 0, g 1 1, ?_, ?_⟩
  · by_contra! e
    have det := g.property
    rw [Matrix.det_fin_two, e.1, e.2] at det
    norm_num at det
  · rw [ModularGroup.denom_apply] at h
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
      add_zero] at h
    change Real.sqrt 3 * (((g 1 0 : ℝ)*(B/A)+g 1 1)*_ +
      ((g 1 0 : ℝ)*(D/A))*_) ≤ 2*(D/A) at h
    dsimp [z, UpperHalfPlane.im] at h
    field_simp [ha.ne'] at h
    apply le_of_mul_le_mul_right (a := A) _ ha
    linear_combination (norm := ring_nf) h + Real.sqrt 3 * (g 1 0 : ℝ)^2 * disc
    norm_num

/-- The planar Hermite inequality for an arbitrary full coordinate lattice. -/
theorem planar_hermite (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ Real.sqrt 3 * (∑ i, (v.val i)^2) ≤ 2 * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let x := (b 0).val
  let y := (b 1).val
  have hc := ZLattice.covolume_pos L MeasureTheory.volume
  have det : ZLattice.covolume L = |x 0*y 1-x 1*y 0| := by
    rw [ZLattice.covolume_eq_det L b, Matrix.det_fin_two]
    rfl
  have ha : 0 < x 0^2+x 1^2 := by
    by_contra! h
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
    simp [det,h0,h1] at hc
  obtain ⟨c,d,hcd,h⟩ := binary_short _ (x 0*y 0+x 1*y 1) (y 0^2+y 1^2) _ ha hc (by
    rw [det, sq_abs]; ring)
  refine ⟨c • b 1 + d • b 0, ?_, ?_⟩
  · intro e
    have h0 := congrArg (fun v : L ↦ b.repr v 0) e
    have h1 := congrArg (fun v : L ↦ b.repr v 1) e
    simp at h0 h1
    tauto
  · simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Pi.add_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
    dsimp [x,y] at h
    linarith only [h]


open SigabaNeo.BKZ InnerProductSpace

noncomputable def weakGamma (k : ℕ) : ℝ :=
  if k = 2 then 2 / Real.sqrt 3 else blichfeldtConstant k

theorem weakGamma_pos (k : ℕ) : 0 < weakGamma k := by
  unfold weakGamma
  split
  · positivity
  · exact blichfeldtConstant_pos _

theorem wall1_small_rank_hermite_weak : HermiteBound weakGamma := by
  intro k _ L _ _
  by_cases hk : k = 2
  · subst k
    obtain ⟨v,hv,h⟩ := planar_hermite L
    refine ⟨v,hv,?_⟩
    norm_num [weakGamma]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [Fin.sum_univ_two] at h
    linarith
  · simpa [weakGamma,hk] using hermite_blichfeldt_coords L

private theorem weak_step (k : ℕ) (hk : 2 ≤ k) : weakGamma k ≤ weakGamma (k+1) := by
  have next : k+1 ≠ 2 := by omega
  simp only [weakGamma, ite_eq_right next]
  split
  · subst k
    apply le_trans _ (blichfeldtConstant_mono (by decide : 0 < 2) (by decide : 2 ≤ 2+1))
    norm_num [blichfeldtConstant, Real.Gamma_nat_eq_factorial]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.pi_lt_d2
    field_simp
    nlinarith [Real.sqrt_nonneg 3]
  · exact blichfeldtConstant_mono (by omega) (by omega)

private theorem weak_penalty_mono {β : ℕ} (hβ : 2 ≤ β) : Monotone (penalty β hβ weakGamma) := by
  have one : 1 ≤ weakGamma 2 := by
    change 1 ≤ 2 / Real.sqrt 3
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have mono (k : ℕ) : 1 ≤ weakGamma (k+2) := by
    induction k with
    | zero => exact one
    | succ k ih => exact ih.trans (weak_step _ (by omega))
  apply penalty_mono hβ _ (Real.log_nonneg one)
  intro l
  apply mul_le_mul (by linarith) _ (by positivity [Real.log_nonneg (mono l)]) (by positivity)
  exact div_le_div_of_nonneg_right (Real.log_le_log (weakGamma_pos _) (weak_step _ (by omega))) (by norm_num)

theorem weak_prefix_ratio {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β)
    (t : Fin n) :
    ‖gramSchmidt ℝ b (firstOfTarget t)‖ * Real.exp (-penalty β hβ weakGamma t.val) ≤
      ‖gramSchmidt ℝ b t‖ :=
  prefix_ratio b hb hr hβ wall1_small_rank_hermite_weak weakGamma_pos t

/-- First-vector threshold for the planar and Blichfeldt profile. -/
theorem weak_ratio_unique {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (R : ℝ) (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} → R < ‖w‖)
    (short : ‖u‖ ≤ R * Real.exp (-penalty β hβ weakGamma (n-β))) :
    b (firstOfBlock hβ hn) = u ∨ b (firstOfBlock hβ hn) = -u :=
  ratio_unique b hb hr hβ hn wall1_small_rank_hermite_weak weakGamma_pos (fun _ hi ↦ weak_penalty_mono hβ hi)
    u hu hne R gap short

#print axioms weak_prefix_ratio
#print axioms weak_ratio_unique
/-- The remaining sharp certificates over an inclusive interval of ranks. -/
def ExactHermiteRange (lo hi : ℕ) : Prop := ∀ (k : ℕ), lo ≤ k → k ≤ hi →
  ∀ (L : Submodule ℤ (Fin k → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤ auditedGamma k * ZLattice.covolume L^(2/(k:ℝ))

theorem smallRankHermite_of_remaining
    (middle : ExactHermiteRange 3 5) (upper : ExactHermiteRange 6 8) : SmallRankHermite := by
  intro k lo hi L hd hf
  rcases eq_or_lt_of_le lo with e | gt
  · subst k
    have eq : auditedGamma 2 = weakGamma 2 := by
      norm_num [auditedGamma, hermitePower, weakGamma]
      rw [div_eq_mul_one_div (Real.log _), ← Real.rpow_def_of_pos (by norm_num : 0 < (4/3:ℝ))]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
      norm_num
    rw [eq]
    exact wall1_small_rank_hermite_weak 2 L
  · by_cases h : k ≤ 5
    · exact middle k (by omega) h L
    · exact upper k (by omega) hi L

end SigabaNeo.Wall1
