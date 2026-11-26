module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Tree

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Real Filter MeasureTheory Metric

/-- Closed Euclidean shell with relative half-width w. -/
def radialShell {E : Type*} [Norm E] (R w : ℝ) : Set E :=
  {v | R * (1-w) ≤ ‖v‖ ∧ ‖v‖ ≤ R * (1+w)}

/-- Normalizing at a ball of volume one eliminates the unit-ball constant. -/
theorem radialShell_volume_le {n : ℕ} {r t w : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hunit : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1) :
    volume.real (radialShell (E := EuclideanSpace ℝ (Fin n)) (t*r) w) ≤ (t*(1+w))^n := by
  have hsub : radialShell (E := EuclideanSpace ℝ (Fin n)) (t*r) w ⊆
      closedBall 0 ((t*(1+w))*r) := by
    intro v hv
    rw [mem_closedBall, dist_zero_right]
    exact hv.2.trans_eq (by ring)
  apply (measureReal_mono hsub (measure_closedBall_lt_top.ne)).trans
  rw [measureReal_def, Measure.addHaar_closedBall_mul volume _ (by positivity) hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp [← measureReal_def, hunit]

/-- The prescribed terminal shell has at most one extra unit in its log-volume
from thickening the outer radius. -/
theorem terminalVolume_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r)
    (hunit : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1) :
    let L : ℝ := ⌈log n⌉₊
    let t := exp (log (4/3)/2 + 1/L)
    volume.real (radialShell (E := EuclideanSpace ℝ (Fin n)) (t*r) ((n:ℝ)^2)⁻¹) ≤
      exp (log (4/3)*n/2 + n/L + 1) := by
  dsimp only
  apply (radialShell_volume_le hr (exp_pos _).le (by positivity) hunit).trans
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < n := by linarith
  have hsmall : (n:ℝ) * ((n:ℝ)^2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr h)]
  calc
    _ ≤ (exp (log (4/3)/2 + 1/(⌈log n⌉₊:ℝ)) * exp (((n:ℝ)^2)⁻¹))^n := by
      gcongr
      linarith [Real.add_one_le_exp (((n:ℝ)^2)⁻¹)]
    _ ≤ _ := by
      rw [← exp_add, ← exp_nat_mul]
      apply exp_le_exp.mpr
      linarith only [hsmall, show (n:ℝ)*(1/(⌈log n⌉₊:ℝ)) = n/(⌈log n⌉₊:ℝ) by ring]

/-- Any fixed polynomial and the loss at all tree levels fit in half the
subexponential slack of the initial list. -/
theorem prescribedSize_reserve (K : ℝ) (hK : 0 ≤ K) (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, (i:ℝ) ≤ K * log n ^ 3 →
      (n:ℝ)^p * exp (log (4/3)*n/2 + 3*n/(2*(⌈log n⌉₊:ℝ))) ≤ prescribedSize n i := by
  let A := K * log 16 + p + 2
  have hA : 0 < A := by dsimp [A]; positivity
  have small := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound
    (show 0 < 1/(4*A) by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually small,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2,
    eventually_ge_atTop 2] with n hn hl hnat
  change 2 ≤ log (n:ℝ) at hl
  change ‖log (n:ℝ)^4‖ ≤ _ * ‖(n:ℝ)‖ at hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (n:ℝ)^4),
    abs_of_nonneg (by positivity : 0 ≤ (n:ℝ))] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hn
  intro i hi
  let L : ℝ := ⌈log n⌉₊
  have hL : 0 < L := lt_of_lt_of_le (by linarith : 0 < log (n:ℝ)) (Nat.le_ceil _)
  have hLu : L ≤ 2*log n := by
    dsimp [L]; linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ log (n:ℝ))]
  have hc : log (n:ℝ) ≤ log n ^ 3 := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ log (n:ℝ)) (by decide : 1 ≤ 3)
  have hcost : 1 + p * log (n:ℝ) + i * log 16 ≤ A * log n ^ 3 := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg p : (0:ℝ) ≤ p),
      mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ log (16:ℝ))]
  have hslack : A * log (n:ℝ)^3 ≤ n/(2*L) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hLu
      (by positivity : 0 ≤ A * log (n:ℝ)^3)]
  let y := log (4/3)*n/2 + 3*n/(2*L)
  let b := (n:ℝ)^p * exp y
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : 1 ≤ b := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    · apply one_le_exp; dsimp [y]; positivity
  have eq : 3*(n:ℝ)/(2*L) + n/(2*L) = 2*n/L := by ring
  have hbase : (b+1)*(16:ℝ)^i ≤ (prescribedSize n 0 : ℝ) := by
    change _ ≤ (⌈exp _⌉₊ : ℝ)
    apply le_trans _ (Nat.le_ceil _)
    calc
      _ ≤ (exp 1 * b)*(16:ℝ)^i := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right (Real.add_one_le_exp 1) ((show (0:ℝ) ≤ 1 by norm_num).trans hb)]
      _ = exp (1 + p*log n + y + i*log 16) := by
        simp [b, exp_add, exp_nat_mul, exp_log hnp, exp_log (by norm_num : (0:ℝ)<16)]
        ring
      _ ≤ _ := by
        apply exp_le_exp.mpr
        change _ ≤ log (4/3)*n/2 + 2*n/L
        dsimp [y]; linarith
  have hr : (prescribedSize n 0 : ℝ) < ((prescribedSize n i : ℝ)+1)*(16:ℝ)^i := by
    exact_mod_cast prescribedSize_rounding n i
  have := lt_of_mul_lt_mul_right (hbase.trans_lt hr) (by positivity : (0:ℝ) ≤ 16^i)
  change b ≤ _
  linarith

/-- S1 implies the terminal occupancy margin at the prescribed radius. -/
theorem terminalOccupancy_eventually {G : Type*} (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m:ℝ) ≤ K * log n ^ 3 →
      ∀ (U : Finset G) (θ r : ℝ), 0 ≤ r →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1 →
      let L : ℝ := ⌈log n⌉₊
      let t := exp (log (4/3)/2 + 1/L)
      S1 U (volume.real (radialShell (E := EuclideanSpace ℝ (Fin n)) (t*r) ((n:ℝ)^2)⁻¹)) θ →
      U.Nonempty → log U.card + n/log n ≤ prescribedSize n m / (U.card:ℝ) := by
  filter_upwards [prescribedSize_reserve K hK 4,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2,
    eventually_ge_atTop 10] with n hsize hl hn
  change 2 ≤ log (n:ℝ) at hl
  intro m hm U θ r hr hunit
  dsimp only
  intro pop hU
  let L : ℝ := ⌈log n⌉₊
  have hL : 1 ≤ L := le_trans (by linarith : 1 ≤ log (n:ℝ)) (Nat.le_ceil _)
  have hN : (10:ℝ) ≤ n := by exact_mod_cast hn
  let a := log (4/3)*(n:ℝ)/2 + n/L
  have hu : (U.card:ℝ) ≤ exp (a+2) := by
    rw [pop.population]
    calc
      _ ≤ exp 1 * exp (a+1) := by
        apply mul_le_mul _ (terminalVolume_le (by omega) hr hunit) measureReal_nonneg (exp_pos _).le
        linarith [pop.upper, Real.add_one_le_exp (1:ℝ)]
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hlog := (Real.log_le_iff_le_exp (by exact_mod_cast hU.card_pos)).2 hu
  have hlin : log U.card + n/log n ≤ (n:ℝ)^2 := by
    dsimp [a] at hlog
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4/3)
    nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n : (0:ℝ) ≤ n),
      div_le_self (Nat.cast_nonneg n : (0:ℝ) ≤ n) hL,
      div_le_self (Nat.cast_nonneg n : (0:ℝ) ≤ n) (by linarith : 1 ≤ log (n:ℝ)),
      mul_nonneg (sub_nonneg.mpr hN) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hsl : n/L ≤ 3*(n:ℝ)/(2*L) := by
    have hp : 0 < L := by linarith
    field_simp
    linarith
  have he : exp 2 ≤ (n:ℝ)^2 := by
    have := (exp_le_exp.mpr hl).trans_eq (exp_log (by linarith : 0 < (n:ℝ)))
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [le_div_iff₀ (by exact_mod_cast hU.card_pos)]
  calc
    _ ≤ (n:ℝ)^2 * exp (a+2) := mul_le_mul hlin hu (by positivity) (by positivity)
    _ ≤ (n:ℝ)^4 * exp (log (4/3)*n/2 + 3*n/(2*L)) := by
      rw [exp_add, show (n:ℝ)^4 = (n:ℝ)^2 * n^2 by ring]
      calc
        _ = ((n:ℝ)^2 * exp 2) * exp a := by ring
        _ ≤ _ := by gcongr; exact add_le_add_right hsl _
    _ ≤ _ := hsize m hm

#print axioms radialShell_volume_le
#print axioms terminalVolume_le
#print axioms prescribedSize_reserve
#print axioms terminalOccupancy_eventually

end SigabaNeo.Lattices.Sieve
