import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExit408
import Definitions.Def_LatticeAttack_Research_Wall1_DualExitCertificate

set_option autoImplicit true

/-! Kernel-checked outward enclosures for the unrounded Part 172 charges. -/

noncomputable section
namespace SigabaNeo.Wall1.DualExit
open MeasureTheory Metric Real Certificate QaryMembership
open scoped BigOperators

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private def ballCoeff (d : ℕ) := (√π)^d / Gamma ((d : ℝ)/2+1)

private theorem ballCoeff_formula (d : ℕ) :
    ballCoeff d = (1 + (d%2 : ℕ) : ℝ) * (2*π)^(d/2) / d.doubleFactorial := by
  induction d using Nat.twoStepInduction with
  | zero => norm_num [ballCoeff, Nat.doubleFactorial, Gamma_one]
  | one =>
    have g : Gamma (3/2) = (1/2)*√π := by
      rw [show (3/2 : ℝ) = 1/2+1 by norm_num, Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0),
        Gamma_one_half_eq]
    norm_num [ballCoeff, Nat.doubleFactorial, g]
    field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]
  | more d ih _ =>
    have step : ballCoeff (d+2) = ballCoeff d * (2*π)/((d : ℝ)+2) := by
      simp only [ballCoeff, Nat.cast_add, Nat.cast_ofNat, pow_add,
        Real.sq_sqrt Real.pi_pos.le, show ((d:ℝ)+2)/2+1 = (d/2+1)+1 by ring,
        Gamma_add_one (by positivity : (d:ℝ)/2+1 ≠ 0)]
      field_simp
    rw [step, ih, Nat.doubleFactorial_add_two, show (d+2)/2 = d/2+1 by omega]
    simp only [Nat.add_mod_right, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, pow_succ,
      div_eq_mul_inv, mul_inv_rev]
    ring

private theorem unitVolume_bounds {ι : Type*} [Fintype ι] [Nonempty ι] (d : ℕ)
    (hd : Fintype.card ι = d) :
    (volumeNum twoPiLo d : ℝ) / volumeDen d ≤ volume.real (ball (0 : EuclideanSpace ℝ ι) 1) ∧
    volume.real (ball (0 : EuclideanSpace ℝ ι) 1) ≤ (volumeNum twoPiHi d : ℝ) / volumeDen d := by
  have hV : volume.real (ball (0 : EuclideanSpace ℝ ι) 1) = ballCoeff d := by
    rw [Measure.real, EuclideanSpace.volume_ball, hd, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity [Real.Gamma_pos_of_pos (by positivity :
        0 < (d:ℝ)/2+1)])]
    rfl
  have rat (p : ℕ) : (volumeNum p d : ℝ) / volumeDen d =
      (1 + (d%2 : ℕ) : ℝ) * ((p:ℝ)/piScale)^(d/2) / d.doubleFactorial := by
    simp only [volumeNum, volumeDen, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      div_pow]
    ring
  rw [hV, ballCoeff_formula, rat, rat]
  have low : (twoPiLo : ℝ) / piScale ≤ 2*π := by norm_num [twoPiLo, piScale]; linarith [pi_gt_d20]
  have high : 2*π ≤ (twoPiHi : ℝ) / piScale := by norm_num [twoPiHi, piScale]; linarith [pi_lt_d20]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) low _) (by positivity)) (by positivity),
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) high _) (by positivity)) (by positivity)⟩

private theorem enclosure (d : ℕ) (Q D L H a c B S P V : ℝ)
    (hd : 0 < (d : ℝ)) (hQ : 0 < Q) (hD : 0 < D) (ha : 0 < a) (hc : 0 < c)
    (hV : 0 < V) (hB : 0 ≤ B) (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hLo : L/D ≤ V) (hHi : V ≤ H/D)
    (hs : 4*S^2 ≤ d*a^2) (hb : (d:ℝ)*a^2 ≤ 4*B^2)
    (hroot : Q*D*a^d ≤ 408000*L*(B+S)^d)
    (hcharge : c^2*H^2*(4*B^2+d*a^2)^d ≤ P^2*D^2*Q^2*(4*a^2)^d) :
    let Y := (Q/(408000*V)) ^ (d : ℝ)⁻¹
    Real.sqrt ((Y - Real.sqrt d/2)^2 + d/4)^d * V / Q ≤ P/c := by
  intro Y
  have sqrt_s := Real.sq_sqrt hd.le
  have sqrt_scaled : (Real.sqrt d*a)^2 = d*a^2 := by rw [mul_pow, sqrt_s]
  have hsqrt : 2*S ≤ Real.sqrt d*a := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hs, sqrt_scaled]
  have hbsqrt : Real.sqrt d*a ≤ 2*B := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hb, sqrt_scaled]
  have hy : Y ≤ (B+S)/a := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hd).mpr
    rw [Real.rpow_natCast, div_pow, div_le_div_iff₀ (by positivity) (pow_pos ha _)]
    have hLD := (div_le_iff₀ hD).mp hLo
    have hh := mul_le_mul_of_nonneg_right hLD (show 0 ≤ 408000*(B+S)^d by positivity)
    apply le_of_mul_le_mul_right (a := D) _ hD
    nlinarith only [hroot, hh]
  have hYpos : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
  have absBound : ((Y - Real.sqrt d/2)*a)^2 ≤ B^2 := by
    apply sq_le_sq'
    · nlinarith only [mul_nonneg hYpos ha.le, hbsqrt]
    · nlinarith only [(le_div_iff₀ ha).mp hy, hsqrt]
  let r := Real.sqrt ((Y - Real.sqrt d/2)^2 + d/4)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 * (4*a^2) ≤ 4*B^2 + d*a^2 := by
    rw [show r^2 = _ from Real.sq_sqrt (show 0 ≤ (Y - Real.sqrt d/2)^2 + d/4 by positivity)]
    nlinarith only [absBound]
  have hrpow := pow_le_pow_left₀ (by positivity) hr2 d
  rw [mul_pow] at hrpow
  have hHi' := (le_div_iff₀ hD).mp hHi
  have hsq := pow_le_pow_left₀ (by positivity) hHi' 2
  have left : (r^d*V*c)^2 * (D^2 * (4*a^2)^d) ≤
      c^2 * H^2 * (4*B^2 + d*a^2)^d := calc
    _ = c^2 * (V*D)^2 * ((r^2)^d * (4*a^2)^d) := by
      have he : (r^2)^d = (r^d)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [he]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hrpow (by positivity)
      (by positivity)
  have finalSq : (r^d*V*c)^2 ≤ (P*Q)^2 := by
    apply le_of_mul_le_mul_right _ (show 0 < D^2*(4*a^2)^d by positivity)
    calc
      _ ≤ _ := left.trans hcharge
      _ = _ := by ring
  have final := (sq_le_sq₀ (by positivity) (by positivity)).mp finalSq
  exact (div_le_div_iff₀ hQ hc).mpr final

/-- The four integer tests imply an outward bound on the charge including both real roots.
The lower side of the squared radius uses the nonnegativity of the original positive root. -/
theorem exitCharge_le_row (t : Fin 408) : exitCharge t ≤ ((row t).2.2 : ℝ) / chargeScale := by
  let n := restartCols t
  let d := 400 + n
  let V := volume.real (ball (0 : Space 400 n) 1)
  let B : ℝ := (row t).1
  let S : ℝ := (row t).2.1
  let P : ℝ := (row t).2.2
  let L : ℝ := volumeNum twoPiLo d
  let H : ℝ := volumeNum twoPiHi d
  let D : ℝ := volumeDen d
  let a : ℝ := scale
  let c : ℝ := chargeScale
  let Q : ℝ := 3329^n
  let Y := (Q/(408000*V)) ^ (d : ℝ)⁻¹
  have eqdim : Fintype.card (Coord 400 n) = d := by simp [d, Coord]
  obtain ⟨hLo, hHi⟩ := unitVolume_bounds (ι := Coord 400 n) d eqdim
  change L/D ≤ V at hLo
  change V ≤ H/D at hHi
  have hD : 0 < D := by dsimp [D, volumeDen]; positivity
  have ha : 0 < a := by norm_num [a, scale]
  have hc : 0 < c := by norm_num [c, chargeScale]
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hd : 0 < (d : ℝ) := by dsimp [d]; positivity
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hP : 0 ≤ P := Nat.cast_nonneg _
  obtain ⟨h₁, h₂, h₃, h₄⟩ := rows_valid t
  have hs := (Nat.cast_le (α := ℝ)).mpr h₁
  have hb := (Nat.cast_le (α := ℝ)).mpr h₂
  have hroot := (Nat.cast_le (α := ℝ)).mpr h₃
  have hcharge := (Nat.cast_le (α := ℝ)).mpr h₄
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hs hb hroot hcharge
  have edim : (400 : ℝ) + (105 + (t.val : ℝ)) = (d : ℝ) := by simp [d, n, restartCols]
  have ea : (10 : ℝ)^8 = a := by simp only [a, Nat.cast_pow, Nat.cast_ofNat]
  have ec : (10 : ℝ)^23 = c := by simp only [c, Nat.cast_pow, Nat.cast_ofNat]
  rw [edim, ea] at hs hb hcharge
  rw [ea] at hroot
  rw [ec] at hcharge
  have hnum : c^2*H^2*(4*B^2+d*a^2)^d ≤ P^2*D^2*Q^2*(4*a^2)^d := by
    dsimp only [Q]
    rw [← pow_mul, Nat.mul_comm n 2]
    exact hcharge
  have radius : 3329 * originalRadius t = Y - Real.sqrt d/2 := by
    unfold originalRadius
    have ed : (400:ℝ) + restartCols t = (d:ℝ) := by simp [d, n]
    dsimp only
    rw [ed]
    dsimp only [Y, V, Q, n]
    ring
  change inwardVolume (Coord 400 n) (3329 * originalRadius t) / Q ≤ P/c
  unfold inwardVolume
  rw [eqdim, radius]
  exact enclosure d Q D L H a c B S P V hd hQ hD ha hc hV hB hS hP hLo hHi hs hb hroot hnum

/-- Sum of the outward bounds at the original Part 142 radii. -/
theorem charge_sum_numeric : (∑ t : Fin 408, exitCharge t) < 8147 / (10:ℝ)^17 := by
  apply lt_of_le_of_lt (Finset.sum_le_sum fun t _ ↦ exitCharge_le_row t)
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have h : ((∑ t : Fin 408, (row t).2.2 : ℕ) : ℝ) < 8147000000 := by exact_mod_cast sum_charges
  apply (div_lt_iff₀ (by norm_num [chargeScale])).mpr
  convert h using 1
  norm_num [chargeScale]

theorem charge406_numeric : exitCharge 406 < 4592 / (10:ℝ)^18 := by
  apply lt_of_le_of_lt (exitCharge_le_row 406)
  have h : ((row 406).2.2 : ℝ) < 459200000 := by exact_mod_cast charge406
  apply (div_lt_iff₀ (by norm_num [chargeScale])).mpr
  convert h using 1
  norm_num [chargeScale]

/-- The simultaneous raw exit is strictly below 8.147 × 10⁻¹⁴. -/
theorem restart_exit_numeric : probability restartExit < 8147 / (10:ℝ)^17 :=
  restart_exit_bound.trans_lt charge_sum_numeric

/-- The draw-406 exit on the same full design is strictly below 4.592 × 10⁻¹⁵. -/
theorem draw406_exit_numeric :
    probability (fun A : Design 400 512 3329 ↦
      rawExit (designPrefix (restartCols_le 406) A) (originalRadius 406)) < 4592 / (10:ℝ)^18 :=
  draw406_exit_bound.trans_lt charge406_numeric

/-- Probability for a reducer with arbitrary design-dependent retained subspaces. -/
theorem retained_exit_numeric
    (S : Design 400 512 3329 → (t : Fin 408) → Submodule ℝ (Space 400 (restartCols t))) :
    probability (fun A ↦ ∃ t : Fin 408,
      ∃ x : (sectionFrame (designPrefix (restartCols_le t) A) (S A t)).Dual,
        x ≠ 0 ∧ ‖x.val‖ < originalRadius t) < 8147 / (10:ℝ)^17 := by
  apply lt_of_le_of_lt _ restart_exit_numeric
  apply probability_mono
  rintro A ⟨t, x, hx, hs⟩
  by_contra good
  exact hs.not_ge (restart_good_floor A good t (S A t) .restart x hx)

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.exitCharge_le_row
#print axioms SigabaNeo.Wall1.DualExit.charge_sum_numeric
#print axioms SigabaNeo.Wall1.DualExit.charge406_numeric
#print axioms SigabaNeo.Wall1.DualExit.restart_exit_numeric
#print axioms SigabaNeo.Wall1.DualExit.draw406_exit_numeric
#print axioms SigabaNeo.Wall1.DualExit.retained_exit_numeric
