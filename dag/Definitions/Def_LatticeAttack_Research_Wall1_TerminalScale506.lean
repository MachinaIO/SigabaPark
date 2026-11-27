import Definitions.Def_LatticeAttack_Research_Wall1_TerminalProjectionCount
import Definitions.Def_LatticeAttack_Research_Wall1_GaussianSmoothing1D

set_option autoImplicit true

/-! # The physical scale of the width-506 terminal restart

Part 183 defines a deterministic lower envelope for the log determinant. The first
20 modulus steps followed by 386 Hermite steps suffice, whether or not a maximum
in the defining recurrence is attained by the chosen branch.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open MeasureTheory Metric

/-- The log determinant lower envelope in Part 183. -/
def terminalLogFloor : ℕ → ℝ
  | 0 => Real.log ((3329 : ℝ)^400)
  | n+1 => max (terminalLogFloor n - Real.log 3329)
      ((505/506) * terminalLogFloor n - Real.log 56.2142 / 2)

/-- Volume of the Euclidean unit ball in the incoming window dimension. -/
def terminalBallVolume : ℝ :=
  volume.real (ball (0 : EuclideanSpace ℝ (Fin 506)) 1)

/-- Gaussian-heuristic scale of a width-506 window of determinant D. -/
def terminalScale (D : ℝ) : ℝ := (D / terminalBallVolume) ^ (1 / (506 : ℝ))

theorem terminalBallVolume_eq : terminalBallVolume = Real.pi^253 / (Nat.factorial 253 : ℝ) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 506)) = 2 * 253 := by simp
  rw [terminalBallVolume, Measure.real, InnerProductSpace.volume_ball_of_dim_even hdim]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^253 / (Nat.factorial 253 : ℝ))]

namespace TerminalInterval

def taylor (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, x^i / i.factorial

private theorem cast_taylor (x : ℚ) (n : ℕ) :
    (taylor x n : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ)^i / i.factorial := by
  simp [taylor]

theorem exp_lower (x a : ℚ) (hx : 0 ≤ x) (ha : a ≤ taylor x 20) :
    (a : ℝ) ≤ Real.exp x :=
  (Rat.cast_le (K := ℝ).2 ha).trans <| (cast_taylor x 20) ▸
    Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) 20

theorem exp_upper (x a : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (ha : taylor x 20 + x^20 * 21 / ((Nat.factorial 20 : ℚ) * 20) ≤ a) :
    Real.exp x ≤ (a : ℝ) := by
  have h := Real.exp_bound' (by exact_mod_cast hx : 0 ≤ (x : ℝ))
    (by exact_mod_cast hx' : (x : ℝ) ≤ 1) (n := 20) (by decide)
  rw [← cast_taylor] at h
  exact h.trans (by exact_mod_cast ha)

end TerminalInterval

open TerminalInterval

private theorem modulus_log : 8.11042723757502 ≤ Real.log 3329 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).2
  let x : ℚ := 8.11042723757502/16
  let a : ℚ := 1.6601396118373724
  have h := exp_upper x a (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : (8.11042723757502 : ℝ) = (16 : ℕ) * (x : ℝ) := by norm_num [x]
  rw [he, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le h 16).trans
    (by exact_mod_cast (show a^16 ≤ 3329 by decide +kernel))

private theorem cap_log : Real.log 56.2142 ≤ 4.02916939402335 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  let x : ℚ := 4.02916939402335/8
  let a : ℚ := 1.6547437686137930
  have h := exp_lower x a (by decide +kernel) (by decide +kernel)
  have he : (4.02916939402335 : ℝ) = (8 : ℕ) * (x : ℝ) := by norm_num [x]
  rw [he, Real.exp_nat_mul]
  refine le_trans ?_ (pow_le_pow_left₀ (by norm_num [a]) h 8)
  have hr := (Rat.cast_le (K := ℝ)).2 (show (562142 / 10000 : ℚ) ≤ a^8 by decide +kernel)
  push_cast at hr
  exact le_trans (by norm_num) hr

private theorem modulus_steps (n : ℕ) :
    (400 - (n : ℝ)) * Real.log 3329 ≤ terminalLogFloor n := by
  induction n with
  | zero => simp [terminalLogFloor, Real.log_pow]
  | succ n ih =>
    refine le_trans ?_ (le_max_left _ _)
    push_cast
    linarith

private theorem hermite_steps (n : ℕ) :
    (505/506 : ℝ)^n * (380 * Real.log 3329 + 253 * Real.log 56.2142) -
      253 * Real.log 56.2142 ≤ terminalLogFloor (20+n) := by
  induction n with
  | zero => simpa using (show 380 * Real.log 3329 ≤ terminalLogFloor 20 by
              convert modulus_steps 20 using 1; norm_num)
  | succ n ih =>
    refine le_trans ?_ (le_max_right _ _)
    rw [pow_succ]
    change _ ≤ 505/506 * terminalLogFloor (20+n) - _
    linarith

theorem terminalLogFloor_406 : 891.78636503830 ≤ terminalLogFloor 406 := by
  let a : ℚ := (505/506)^386
  have ha : (a : ℝ) = (505/506 : ℝ)^386 := by simp [a]
  have ha0 : 0 ≤ (a : ℝ) := by rw [ha]; positivity
  have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast (show a ≤ 1 by decide +kernel)
  have h := hermite_steps 386
  rw [← ha] at h
  refine le_trans ?_ h
  have hnum : (891.78636503830 : ℚ) ≤
      a * (380 * 8.11042723757502) - (1-a) * (253 * 4.02916939402335) := by decide +kernel
  have hreal : (891.78636503830 : ℝ) ≤
      (a : ℝ) * (380 * 8.11042723757502) - (1-a) * (253 * 4.02916939402335) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hnum
    norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one, Rat.cast_ofScientific] at hcast
    convert hcast using 1 <;> ring
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr modulus_log),
    mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr cap_log)]

/-- Strict physical scale floor, using the actual Euclidean ball volume. -/
theorem terminalScale_406 : 31.9457118986 < terminalScale (Real.exp (terminalLogFloor 406)) := by
  let x : ℚ := 891.78636503830/1024
  let a : ℚ := 2.38902449636788
  let p : ℚ := 3.14159265358979323847
  have he : (891.78636503830 : ℝ) = (1024 : ℕ) * (x : ℝ) := by norm_num [x]
  have h := exp_lower x a (by decide +kernel) (by decide +kernel)
  have hd := Real.exp_le_exp.mpr terminalLogFloor_406
  rw [he, Real.exp_nat_mul] at hd
  have hlo := (pow_le_pow_left₀ (by norm_num [a]) h 1024).trans hd
  have hp : Real.pi ≤ (p : ℝ) := by simpa [p] using Real.pi_lt_d20.le
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  rw [terminalScale, one_div]
  apply (Real.lt_rpow_inv_iff_of_pos (by norm_num) (div_nonneg (Real.exp_pos _).le hv.le)
    (by norm_num)).2
  rw [show (506 : ℝ) = (506 : ℕ) by norm_num, Real.rpow_natCast]
  apply (lt_div_iff₀ hv).2
  rw [terminalBallVolume_eq, ← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity)).2
  calc
    _ ≤ (31.9457118986 : ℝ)^506 * (p : ℝ)^253 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hp _) (by positivity)
    _ < (a : ℝ)^1024 * (Nat.factorial 253 : ℝ) := by
      have hh := (Rat.cast_lt (K := ℝ)).2 (show (31.9457118986 : ℚ)^506 * p^253 < a^1024 * (Nat.factorial 253)
        by decide +kernel)
      push_cast at hh
      exact hh
    _ ≤ _ := mul_le_mul_of_nonneg_right hlo (by positivity)

/-- Transfer the envelope to the retained determinant using both physical winner caps
and the determinant quotient at each step. -/
theorem terminalScale_of_winners (D s : ℕ → ℝ) (hinit : D 0 = (3329 : ℝ)^400)
    (hs : ∀ i < 406, 0 < s i) (hstep : ∀ i < 406, D (i+1) = D i / s i)
    (hq : ∀ i < 406, s i ≤ 3329)
    (hc : ∀ i < 406, s i ≤ Real.sqrt 56.2142 * (D i)^(1 / (506 : ℝ))) :
    31.9457118986 < terminalScale (D 406) := by
  have path (i : ℕ) (hi : i ≤ 406) : 0 < D i ∧ terminalLogFloor i ≤ Real.log (D i) := by
    induction i with
    | zero => rw [hinit]; exact ⟨by positivity, le_rfl⟩
    | succ i ih =>
      have hi' : i < 406 := by omega
      obtain ⟨hp, hL⟩ := ih hi'.le
      have hs' := hs i hi'
      rw [hstep i hi']
      refine ⟨div_pos hp hs', ?_⟩
      rw [terminalLogFloor, Real.log_div hp.ne' hs'.ne', max_le_iff]
      have hq' := Real.log_le_log hs' (hq i hi')
      have hc' := Real.log_le_log hs' (hc i hi')
      rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by norm_num),
        Real.log_rpow hp] at hc'
      constructor <;> linarith
  obtain ⟨hp, hL⟩ := path 406 le_rfl
  have hd := Real.exp_le_exp.mpr hL
  rw [Real.exp_log hp] at hd
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  exact terminalScale_406.trans_le (Real.rpow_le_rpow (by positivity : 0 ≤
    Real.exp (terminalLogFloor 406) / terminalBallVolume) (div_le_div_of_nonneg_right hd hv.le)
      (by norm_num))

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.terminalLogFloor_406
#print axioms SigabaNeo.Wall1.TerminalProjection.terminalScale_406
#print axioms SigabaNeo.Wall1.TerminalProjection.terminalScale_of_winners
