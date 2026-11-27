import Definitions.Def_LatticeAttack_Research_Wall1_ControlledDrawLaw

set_option autoImplicit true

/-! Rational upper certificates for the three late Gaussian sums in Part 192.
A backward determinant enclosure fixes the last term. All earlier terms are
bounded by a geometric series, with a different ratio for the two horizons. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open Real TerminalProjection TerminalInterval DualExit Finset

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem exp_lower_power (x a : ℚ) (n : ℕ) (hx : 0 ≤ x/n)
    (h : a ≤ taylor (x/n) 20) (ha : 0 ≤ a) (hn : 0 < n) :
    ((a^n : ℚ) : ℝ) ≤ exp x := by
  have e : (x:ℝ) = (n:ℝ)*((x/n:ℚ):ℝ) := by push_cast; field_simp
  rw [e, exp_nat_mul, Rat.cast_pow]
  exact pow_le_pow_left₀ (by exact_mod_cast ha) (exp_lower _ _ hx h) _

private theorem log_bounds : 4 ≤ log 3329 ∧ 4.02916938 ≤ log 56.2142 := by
  have h := exp_upper (4.02916938/8) 1.654743766 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have e : (4.02916938 : ℝ) = (8:ℕ)*((4.02916938/8:ℚ):ℝ) := by norm_num
  have ha : (4.02916938 : ℝ) ≤ log 56.2142 := by
    apply (le_log_iff_exp_le (by norm_num)).2
    rw [e, exp_nat_mul]
    apply (pow_le_pow_left₀ (exp_pos _).le h 8).trans
    norm_num
  exact ⟨(by norm_num : (4:ℝ) ≤ 4.02916938) |>.trans (ha.trans
    (log_le_log (by norm_num) (by norm_num))), ha⟩

private def back : ℕ → ℚ
  | 0 => 891.78636503830
  | j+1 => (back j + 4.02916938/2)*506/505

private theorem back_le (j : ℕ) (hj : j ≤ 13) :
    (back j : ℝ) ≤ terminalLogFloor (406-j) := by
  induction j with
  | zero => exact (by norm_num [back] : ((back 0:ℚ):ℝ) = 891.78636503830) ▸ terminalLogFloor_406
  | succ j ih =>
    have h := ih (by omega)
    rw [show 406-j = (406-(j+1))+1 by omega, terminalLogFloor] at h
    have check : ∀ i : Fin 13, back (i.val+1) ≤ back i + 4 := by decide +kernel
    have hc : (back (j+1):ℝ) ≤ (back j:ℝ)+4 := by exact_mod_cast check ⟨j,by omega⟩
    rcases le_max_iff.mp h with h | h
    · linarith [log_bounds.1]
    · simp only [back, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
        Rat.cast_ofScientific] at *
      linarith [log_bounds.2]

private theorem reverse_step {lo δ : ℝ} (hδ : δ ≤ 4) (hs : 505*δ ≤ lo + 253*4.02916938)
    {k : ℕ} (h : lo ≤ terminalLogFloor (k+1)) :
    terminalLogFloor (k+1) + δ ≤ terminalLogFloor k := by
  rw [terminalLogFloor] at h ⊢
  rcases max_choice (terminalLogFloor k - log 3329)
      (505/506 * terminalLogFloor k - log 56.2142 / 2) with he | he
  · rw [he]; linarith [log_bounds.1]
  · rw [he] at h ⊢; linarith [log_bounds.2]

private theorem geom_bound (N : ℕ) {lo δ x v : ℝ}
    (hl : lo ≤ terminalLogFloor N) (hδ : 0 ≤ δ) (hδ' : δ ≤ 4)
    (hs : 505*δ ≤ lo + 253*4.02916938) (hx : exp (-δ) ≤ x) (hx' : x < 1) :
    (∑ t : Fin (N+1), exp (v-terminalLogFloor t.val)) ≤ exp (v-lo)/(1-x) := by
  have floor' (k) (hk : k ≤ N) : lo ≤ terminalLogFloor k :=
    Nat.decreasingInduction' (motive := fun i ↦ lo ≤ terminalLogFloor i)
      (fun _ _ _ h ↦ by linarith [reverse_step hδ' hs h]) hk hl
  have step (k) (hk : k < N) : exp (v-terminalLogFloor k) ≤
      x * exp (v-terminalLogFloor (k+1)) := by
    have hr := reverse_step hδ' hs (floor' (k+1) hk)
    calc _ ≤ exp ((-δ)+(v-terminalLogFloor (k+1))) := exp_le_exp.mpr (by linarith)
         _ ≤ _ := (exp_add ..).le.trans (mul_le_mul_of_nonneg_right hx (exp_pos _).le)
  have partialSum (k) (hk : k ≤ N) : (∑ i : Fin (k+1), exp (v-terminalLogFloor i.val)) ≤
      exp (v-terminalLogFloor k)/(1-x) := by
    induction k with
    | zero =>
      change (∑ i : Fin 1, exp (v-terminalLogFloor i.val)) ≤ _
      rw [Fin.sum_univ_one]
      change exp (v-terminalLogFloor 0) ≤ _
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith [mul_nonneg (exp_pos (v-terminalLogFloor 0)).le ((exp_pos _).le.trans hx)]
    | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      change (∑ i : Fin (k+1), exp (v-terminalLogFloor i.val)) + exp (v-terminalLogFloor (k+1)) ≤ _
      have hb := (le_div_iff₀ (by linarith : 0 < 1-x)).mp (ih (by omega))
      apply (le_div_iff₀ (by linarith)).mpr
      linarith [step k (by omega)]
  exact (partialSum N le_rfl).trans (div_le_div_of_nonneg_right
    (exp_le_exp.mpr (by linarith)) (by linarith))

private theorem theta_upper {z : ℝ} (hz : 3.2 ≤ z) :
    terminalTheta z ≤ 1.0000000001 := by
  have h := exp_lower_power 30 2.55 32 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide)
  have h30 : (10:ℝ)^12 ≤ exp 30 := by
    apply le_trans _ h
    exact_mod_cast (show (10:ℚ)^12 ≤ 2.55^32 by decide +kernel)
  have hπ := Real.pi_gt_three
  have harg : 30 ≤ π*z^2 := by
    nlinarith [sq_nonneg (z-3.2), mul_nonneg (sub_nonneg.mpr hπ.le) (sq_nonneg z)]
  have hneg : exp (-π*z^2) ≤ 1/10^12 := by
    rw [neg_mul, exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (h30.trans (exp_le_exp.mpr harg))
  have h3 : exp (-3*π*z^2) ≤ 1/10^12 :=
    (exp_le_exp.mpr (by linarith : -3*π*z^2 ≤ -π*z^2)).trans hneg
  unfold terminalTheta
  have hd : 0 < 1 - exp (-3*π*z^2) := by linarith
  have hn : 2*exp (-π*z^2)/(1-exp (-3*π*z^2)) ≤ 0.0000000001 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

private theorem radius_bounds :
    33.22504 ≤ winnerRadius ∧ winnerRadius ≤ 33.22504143 ∧
      30.02221 ≤ planeRadius ∧ planeRadius ≤ 30.02221401 := by
  have a : (1.41421356237:ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have b : √2 ≤ 1.41421356238 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  have c : (1.73205080756:ℝ) ≤ √3 := le_sqrt_of_sq_le (by norm_num)
  have d : √3 ≤ 1.73205080757 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  unfold winnerRadius planeRadius areaCut
  have h3 : 0 < √(3:ℝ) := by positivity
  rw [mul_div_assoc', mul_div_assoc']
  constructor
  · apply le_sqrt_of_sq_le; apply (le_div_iff₀ h3).mpr; linarith
  constructor
  · apply (sqrt_le_left (by norm_num)).mpr; apply (div_le_iff₀ h3).mpr; linarith
  have he : (2:ℝ)*1352/√3/√3 = 2704/3 := by
    rw [div_div, ← sq, sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  rw [he]
  constructor
  · apply le_sqrt_of_sq_le; norm_num
  · apply (sqrt_le_left (by norm_num)).mpr; norm_num

/-- A rational certificate for a complete sum of ball charges. All transcendental
quantities are bounded at a single endpoint or by the geometric ratio. -/
private theorem charge_certificate (N b : ℕ) (r f : ℝ) (lo δ x U F a p : ℚ)
    (hf : 0 < f) (hF : f ≤ F) (hl : (lo:ℝ) ≤ terminalLogFloor N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 4) (hs : 505*δ ≤ lo+253*4.02916938)
    (ratio : (1/x) ≤ taylor δ 20) (hx : 0 < x) (hx' : x < 1)
    (lower : 0 ≤ (lo-b/2)/1024) (ht : a ≤ taylor ((lo-b/2)/1024) 20) (ha : 0 < a)
    (hz : 3.2 ≤ r * √(2*π/b)) (hU : r * √(2*π/b) ≤ U)
    (cert : U^b * (1.0000000001:ℚ)^(b-1) * F / (2*a^1024*(1-x)) < p) :
    (∑ i : Fin (N+1), ballCharge b r (terminalLogFloor i.val - log f)) < (p:ℝ) := by
  let z := r*√(2*π/b)
  have hz' : 0 ≤ z := by dsimp [z]; linarith
  have hθ := theta_upper hz
  have hθ0 : 0 ≤ terminalTheta z := by
    have he : exp (-3*π*z^2) < 1 := exp_lt_one_iff.mpr (by
      have : 0 < z := by dsimp [z]; linarith
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) pi_pos) (sq_pos_of_pos this))
    unfold terminalTheta; positivity [sub_pos.mpr he]
  have he := exp_lower δ (1/x) hδ ratio
  have hx0 : 0 < (x:ℝ) := by exact_mod_cast hx
  have hx1 : (x:ℝ) < 1 := by exact_mod_cast hx'
  have hxδ : exp (-(δ:ℝ)) ≤ x := by
    rw [exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos _)]
    exact (div_le_iff₀ hx0).mp (by simpa using he) |>.trans_eq (mul_comm ..)
  have summ := geom_bound (v := (b:ℝ)/2) N hl (by exact_mod_cast hδ)
    (by exact_mod_cast hδ') (by simpa using (Rat.cast_le (K := ℝ)).2 hs) hxδ hx1
  have hpow := exp_lower_power (lo-b/2) a 1024 lower ht ha.le (by decide)
  have ea : exp ((b:ℝ)/2 - lo) ≤ 1/(a:ℝ)^1024 := by
    rw [← neg_sub, exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (pow_pos (by exact_mod_cast ha) _)
    simpa using hpow
  have e (i : Fin (N+1)) : ballCharge b r (terminalLogFloor i.val - log f) =
      (z^b * terminalTheta z^(b-1)*f/2)*exp ((b:ℝ)/2-terminalLogFloor i.val) := by
    unfold ballCharge
    rw [show (b:ℝ)/2-(terminalLogFloor i.val-log f) = (b/2-terminalLogFloor i.val)+log f by ring,
      exp_add, exp_log hf]
    dsimp [z]; ring
  simp_rw [e]
  rw [← mul_sum]
  have hconst := mul_le_mul (pow_le_pow_left₀ hz' hU b)
    (pow_le_pow_left₀ hθ0 hθ (b-1)) (pow_nonneg hθ0 _) (pow_nonneg (hz'.trans hU) _)
  have hc := div_le_div_of_nonneg_right (mul_le_mul hconst hF hf.le
    (mul_nonneg (pow_nonneg (hz'.trans hU) _) (by positivity))) (by norm_num : (0:ℝ) ≤ 2)
  have hsum := summ.trans (div_le_div_of_nonneg_right ea (by linarith))
  apply lt_of_le_of_lt (mul_le_mul hc hsum (sum_nonneg (fun _ _ ↦ (exp_pos _).le))
    (by positivity [hf.le.trans hF, hz'.trans hU])) _
  have hreal := (Rat.cast_lt (K := ℝ)).2 cert
  push_cast at hreal
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, one_mul] using hreal

private theorem scale506 :
    0.11 ≤ √(2*π/506) ∧ √(2*π/506) ≤ 0.1114332189 := by
  exact ⟨le_sqrt_of_sq_le (by linarith [Real.pi_gt_d2]),
    (sqrt_le_left (by norm_num)).mpr (by linarith [Real.pi_lt_d20])⟩

private theorem scale505 :
    0.11 ≤ √(2*π/505) ∧ √(2*π/505) ≤ 0.11154349425 := by
  exact ⟨le_sqrt_of_sq_le (by linarith [Real.pi_gt_d2]),
    (sqrt_le_left (by norm_num)).mpr (by linarith [Real.pi_lt_d20])⟩

private theorem floor393 : (941.57350 : ℝ) ≤ terminalLogFloor 393 :=
  le_trans (by simpa using (Rat.cast_le (K := ℝ)).2 (show (941.57350 : ℚ) ≤ back 13 by decide +kernel)) (back_le 13 le_rfl)

private theorem floor405 : (895.57085 : ℝ) ≤ terminalLogFloor 405 :=
  le_trans (by simpa using (Rat.cast_le (K := ℝ)).2 (show (895.57085 : ℚ) ≤ back 1 by decide +kernel)) (back_le 1 (by decide))

theorem positive394_sum :
    (∑ i : Fin 394, ballCharge 506 winnerRadius (terminalLogFloor i.val)) < 2.067 / (10:ℝ)^12 := by
  have lo := mul_le_mul radius_bounds.1 scale506.1 (by norm_num) (by linarith [radius_bounds.1])
  have hi := mul_le_mul radius_bounds.2.1 scale506.2 (sqrt_nonneg _) (by norm_num)
  have h := charge_certificate 393 506 winnerRadius 1 941.57350 3.88307
    0.02059 3.70237334 1 1.95900180 (2.067/10^12)
    (by norm_num) (by norm_num) (by simpa using floor393)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num only [Nat.cast_ofNat]; linarith) (by norm_num only [Nat.cast_ofNat, Rat.cast_ofScientific]; linarith)
    (by decide +kernel)
  simpa only [log_one, sub_zero, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific] using h

theorem positive30_sum :
    (∑ i : Fin 406, ballCharge 506 30 (terminalLogFloor i.val)) < 7.190 / (10:ℝ)^15 := by
  have h := charge_certificate 405 506 30 1 895.57085 3.79197
    0.022552 3.34299659 1 1.87294226 (7.190/10^15)
    (by norm_num) (by norm_num) (by simpa using floor405)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num only [Nat.cast_ofNat]; linarith [scale506.1])
    (by norm_num only [Nat.cast_ofNat, Rat.cast_ofScientific]; linarith [scale506.2]) (by decide +kernel)
  simpa only [log_one, sub_zero, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific] using h

theorem horizontal406_sum :
    (∑ i : Fin 406, ballCharge 505 planeRadius (terminalLogFloor i.val - log winnerRadius)) <
      1.038 / (10:ℝ)^13 := by
  have lo := mul_le_mul radius_bounds.2.2.1 scale505.1 (by norm_num) (by linarith [radius_bounds.2.2.1])
  have hi := mul_le_mul radius_bounds.2.2.2 scale505.2 (sqrt_nonneg _) (by norm_num)
  have h := charge_certificate 405 505 planeRadius winnerRadius 895.57085 3.79197
    0.022552 3.34878268 33.225042 1.87385700 (1.038/10^13)
    (by linarith [radius_bounds.1]) (by norm_num only [Rat.cast_ofScientific]; linarith [radius_bounds.2.1])
    (by simpa using floor405)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num only [Nat.cast_ofNat]; linarith) (by norm_num only [Nat.cast_ofNat, Rat.cast_ofScientific]; linarith)
    (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific] using h

theorem prefix_numeric (hp : PrefixEstimates)
    (hs : (∑ u, flagCharge u) ≤ 5.28399 / (10:ℝ)^15) :
    probability Prefix < 5.284 / (10:ℝ)^15 := by
  linarith [prefix_first_moment hp]

theorem good_numeric (hp : PrefixEstimates) (hl : LateEstimates)
    (hs : (∑ u, flagCharge u) ≤ 5.28399 / (10:ℝ)^15) :
    probability (fun A ↦ Good A ∧ terminalHit A) <
      probability residual₁ + probability residual₂ + 2.184 / (10:ℝ)^12 := by
  linarith only [good_first_moment hl, prefix_numeric hp hs, positive394_sum,
    positive30_sum, horizontal406_sum]

theorem terminal_numeric (hp : PrefixEstimates) (hl : LateEstimates)
    (hs : (∑ u, flagCharge u) ≤ 5.28399 / (10:ℝ)^15) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515 / (10:ℝ)^12 := by
  linarith only [terminal_first_moment hl, prefix_numeric hp hs, positive394_sum,
    positive30_sum, horizontal406_sum]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.positive394_sum
#print axioms SigabaNeo.Wall1.ControlledPlane.positive30_sum
#print axioms SigabaNeo.Wall1.ControlledPlane.horizontal406_sum
#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_numeric
#print axioms SigabaNeo.Wall1.ControlledPlane.good_numeric
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_numeric
