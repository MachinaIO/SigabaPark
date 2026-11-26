import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExit

set_option autoImplicit true

/-! Original Part 142 radii, with the Part 172 symbolic charge on all 408 prefixes. -/

noncomputable section
namespace SigabaNeo.Wall1.DualExit
open QaryMembership MeasureTheory Metric
open scoped BigOperators

/-- Number of vertical columns at the zero-based paper index. -/
def restartCols (t : Fin 408) : ℕ := 105 + t.val

theorem restartCols_le (t : Fin 408) : restartCols t ≤ 512 := by
  unfold restartCols
  omega

/-- Part 142 radius with the original allocation 1/408000, before rounding. -/
def originalRadius (t : Fin 408) : ℝ :=
  let n := restartCols t
  let N : ℝ := 400 + n
  let V := volume.real (ball (0 : Space 400 n) 1)
  (((3329 : ℝ)^n / (408000 * V)) ^ N⁻¹ - Real.sqrt N / 2) / 3329

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem unit_volume_lower {ι : Type*} [Fintype ι] (hd : Fintype.card ι ≤ 912) :
    (1 / 16 : ℝ)^Fintype.card ι ≤ volume.real (ball (0 : EuclideanSpace ℝ ι) 1) := by
  let C : Set (ι → ℝ) := Set.univ.pi fun _ ↦ Set.Ioo (-1/32) (1/32)
  have incl : C ⊆ WithLp.toLp 2 ⁻¹' ball (0 : EuclideanSpace ℝ ι) 1 := by
    intro x hx
    change dist (WithLp.toLp 2 x) 0 < 1
    rw [dist_zero_right, ← sq_lt_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq]
    have he : ∑ i, x i ^ 2 ≤ ∑ _ : ι, (1/32 : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨a,b⟩ := hx i (Set.mem_univ _)
      exact sq_le_sq' (by linarith) b.le
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
    have hd' : (Fintype.card ι : ℝ) ≤ 912 := by exact_mod_cast hd
    change ∑ i, x i ^ 2 < _
    linarith
  have v := measure_mono (μ := volume) incl
  rw [(PiLp.volume_preserving_toLp ι).measure_preimage measurableSet_ball.nullMeasurableSet] at v
  have hh := ENNReal.toReal_mono measure_ball_lt_top.ne v
  simp only [C, volume_pi_pi, Real.volume_Ioo, Finset.prod_const, Finset.card_univ,
    ENNReal.toReal_pow] at hh
  norm_num at hh ⊢
  exact hh

/-- The exact original radii satisfy the upper cutoff needed for the nonzero-label argument. -/
theorem originalRadius_le_one (t : Fin 408) : originalRadius t ≤ 1 := by
  let n := restartCols t
  let N := 400 + n
  let V := volume.real (ball (0 : Space 400 n) 1)
  have hn : n ≤ 512 := restartCols_le t
  have hN : N ≤ 912 := by dsimp [N]; omega
  have hc : Fintype.card (Coord 400 n) = N := by simp [Coord, N]
  have hV : (1/16 : ℝ)^N ≤ V := hc ▸ unit_volume_lower (ι := Coord 400 n) (hc ▸ hN)
  have hvpos : 0 < V := lt_of_lt_of_le (by positivity) hV
  have scales : (16 : ℝ)^N ≤ 3329^400 := calc
    (16 : ℝ)^N ≤ 16^1000 := pow_le_pow_right₀ (by norm_num) (show N ≤ 1000 by omega)
    _ = (16^5)^200 := by rw [← pow_mul]
    _ ≤ (3329^2)^200 := pow_le_pow_left₀ (by norm_num) (by norm_num) 200
    _ = _ := by rw [← pow_mul]
  have base : (3329 : ℝ)^n / (408000 * V) ≤ 3329^N := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hprod : (16 : ℝ)^N * 3329^n ≤ 3329^N := by
      rw [show (3329 : ℝ)^N = 3329^400 * 3329^n by rw [← pow_add]]
      exact mul_le_mul_of_nonneg_right scales (by positivity)
    have hprod' : (3329 : ℝ)^n ≤ 3329^N * (1/16)^N := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
      exact hprod
    have enlarge : (1/16 : ℝ)^N ≤ 408000*V :=
      hV.trans (le_mul_of_one_le_left hvpos.le (by norm_num))
    exact hprod'.trans (mul_le_mul_of_nonneg_left enlarge (pow_nonneg (by norm_num) _))
  have hNp : 0 < (N : ℝ) := by dsimp [N]; positivity
  have root : ((3329 : ℝ)^n / (408000 * V)) ^ (N : ℝ)⁻¹ ≤ 3329 := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) hNp).mpr
    simpa using base
  change (_ - Real.sqrt (400 + (n : ℝ)) / 2) / 3329 ≤ 1
  have he : (400 : ℝ) + n = (N : ℝ) := by simp [N]
  rw [he]
  change (((3329 : ℝ)^n / (408000 * V)) ^ (N : ℝ)⁻¹ - Real.sqrt N / 2) / 3329 ≤ 1
  linarith [Real.sqrt_nonneg (N : ℝ)]

/-- Part 172's single-index upper-bound expression at the unrounded Part 142 radius. -/
def exitCharge (t : Fin 408) : ℝ :=
  inwardVolume (Coord 400 (restartCols t)) (3329 * originalRadius t) /
    (3329 : ℝ)^(restartCols t)

def restartExit (A : Design 400 512 3329) : Prop :=
  ∃ t : Fin 408, rawExit (designPrefix (restartCols_le t) A) (originalRadius t)

/-- Equation (4), before numerical evaluation of its right-hand side. -/
theorem restart_exit_bound : probability restartExit ≤ ∑ t : Fin 408, exitCharge t :=
  pass_probability restartCols restartCols_le originalRadius originalRadius_le_one

/-- The single draw-406 charge, measured on the same full 512-column sample space. -/
theorem draw406_exit_bound :
    probability (fun A : Design 400 512 3329 ↦
      rawExit (designPrefix (restartCols_le 406) A) (originalRadius 406)) ≤ exitCharge 406 :=
  (prefix_probability (restartCols_le 406)
    (fun B : Design 400 (restartCols 406) 3329 ↦ rawExit B (originalRadius 406))).le.trans
    (rawExit_probability (originalRadius_le_one 406))

/-- One good full draw gives all index-specific floors, for every choice of retained section.
Each floor also holds for all later marked descendants of that section. -/
theorem restart_good_floor (A : Design 400 512 3329) (good : ¬restartExit A) (t : Fin 408)
    (S : Submodule ℝ (Space 400 (restartCols t))) {F : MarkedFrame (Fin 400) 3329}
    (path : MarkedHistory (sectionFrame (designPrefix (restartCols_le t) A) S) F)
    (x : F.Dual) (hx : x ≠ 0) : originalRadius t ≤ ‖x.val‖ :=
  good_prefix_floor _ (originalRadius_le_one t) (fun h ↦ good ⟨t, h⟩) S path x hx

/-- First-minimum form of the good-event guarantee, including any later marked history. -/
theorem restart_good_minimum (A : Design 400 512 3329) (good : ¬restartExit A) (t : Fin 408)
    (S : Submodule ℝ (Space 400 (restartCols t))) {F : MarkedFrame (Fin 400) 3329}
    (path : MarkedHistory (sectionFrame (designPrefix (restartCols_le t) A) S) F)
    (hF : F.Dual ≠ ⊥) : originalRadius t ≤ ZLattice.minimum F.Dual := by
  apply (ZLattice.le_minimum_iff hF).mpr
  intro x hx hx0
  exact restart_good_floor A good t S path ⟨x, hx⟩ (fun e ↦ hx0 (congrArg Subtype.val e))

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.originalRadius_le_one
#print axioms SigabaNeo.Wall1.DualExit.restart_exit_bound
#print axioms SigabaNeo.Wall1.DualExit.draw406_exit_bound
#print axioms SigabaNeo.Wall1.DualExit.restart_good_floor
#print axioms SigabaNeo.Wall1.DualExit.restart_good_minimum
