module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionCBD
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.Ring.GeomSum

set_option autoImplicit true

public section
namespace SigabaNeo.SampleDeletion
open Polynomial
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 8192

private noncomputable def theta (J : ℕ) : ℕ[X] :=
  ∑ a ∈ Finset.Icc (-(J.sqrt : ℤ)) (J.sqrt : ℤ), X^(a.natAbs^2)
private noncomputable def cumulative (J : ℕ) : ℕ[X] := ∑ i ∈ Finset.range (J+1), X^i
noncomputable def cbd (η : ℕ) : ℕ[X] :=
  ∑ a : Digit η, C (mass a) * X^(energy a)

private theorem ball_coeff (J d k : ℕ) (hk : k ≤ J) :
    ((cumulative J)*(theta J)^d).coeff k = ballCount d k := by
  induction d generalizing k with
  | zero => simp [cumulative, finsetSum_coeff, coeff_X_pow, ballCount, Finset.mem_range, hk]
  | succ d ih =>
    rw [pow_succ, ← mul_assoc, theta, Finset.mul_sum, finsetSum_coeff, ballCount]
    simp_rw [coeff_mul_X_pow']
    let S (j : ℕ) := Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ)
    have hm (a : ℤ) (j : ℕ) : a ∈ S j ↔ a.natAbs^2 ≤ j := by
      dsimp [S]
      rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs, Nat.cast_le, pow_two, ← Nat.le_sqrt]
    apply (Finset.sum_subset_zero_on_sdiff (s₁ := S k) (s₂ := S J) _ _ _).symm
    · exact fun a ha ↦ (hm a J).mpr (((hm a k).mp ha).trans hk)
    · intro a ha
      simp only [Finset.mem_sdiff] at ha
      simp [show ¬ a.natAbs^2 ≤ k from fun h ↦ ha.2 ((hm _ _).mpr h)]
    · intro a ha
      rw [ite_eq_left ((hm _ _).mp ha)]
      exact (ih _ ((Nat.sub_le _ _).trans hk)).symm

theorem cbd_coeff (η d k : ℕ) : ((cbd η)^d).coeff k = shell η d k := by
  induction d generalizing k with
  | zero => simp [shell, coeff_one]
  | succ d ih =>
    rw [pow_succ, cbd, Finset.mul_sum, finsetSum_coeff, shell]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, coeff_mul_X_pow']
    split_ifs
    · change ((cbd η ^ d)* C (mass a)).coeff _ = _
      rw [coeff_mul_C, ih, Nat.mul_comm]
    · rfl

private theorem digit_coeff (p : ℕ[X]) {b : ℕ} (hb : p.eval 1 < b) (k : ℕ) :
    p.eval b / b^k % b = p.coeff k := by
  induction k generalizing p
  all_goals
   have eval' (z : ℕ) : p.eval z = p.divX.eval z * z + p.coeff 0 := by
    simpa using congrArg (Polynomial.eval z) (divX_mul_X_add p).symm
   have h := eval' 1
   simp only [mul_one] at h
   have h0 : p.coeff 0 < b := by omega
  case zero => simp [eval', Nat.mod_eq_of_lt h0]
  case succ k ih =>
    rw [pow_succ', ← Nat.div_div_eq_div_mul, eval', Nat.add_comm,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h0, zero_add,
      ih p.divX (by omega), coeff_divX]

/-- Reduce the word modulo a power of the base before extracting its kth digit. -/
private theorem packed_coeff (p : ℕ[X]) (b k l : ℕ) (hk : k < l) (hb : p.eval 1 < b)
    (w : ℕ) (hw : w ≡ p.eval b [MOD b^l]) :
    w / b^k % b = p.coeff k := by
  rw [← digit_coeff p hb k, ← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self]
  rw [← pow_succ]
  exact congrArg (· / b^k) (hw.of_dvd (pow_dvd_pow _ hk))

/-- Structural summation for small finite coordinate alphabets. -/
@[expose] def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumTo f n + f n

private theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ k ∈ Finset.range n, f k := by
  induction n with | zero => simp [sumTo] | succ _ ih => simp [sumTo, ih, Finset.sum_range_succ]

@[expose] def thetaWord (b : ℕ) := sumTo (fun a ↦ b ^ ((Int.ofNat a - 44).natAbs^2)) 89
@[expose] def cbdWord (b : ℕ) := sumTo (fun a ↦ (Nat.choose 6 a) * b ^ ((Int.ofNat a - 3).natAbs^2)) 7

private theorem eval_theta (b : ℕ) : (theta 2000).eval b = thetaWord b := by
  simp only [theta, eval_finsetSum, eval_pow, eval_X, thetaWord, sumTo_eq]
  have he : Finset.Icc (-(Nat.sqrt 2000 : ℤ)) (Nat.sqrt 2000 : ℤ) =
      (Finset.range 89).map ⟨fun a : ℕ ↦ (a : ℤ)-44, by intro a c h; change (a : ℤ)-44 = (c : ℤ)-44 at h; omega⟩ := by
    ext a
    rw [show Nat.sqrt 2000 = 44 from Nat.le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by decide : 2000 < 45*45))) (Nat.le_sqrt.mpr (by decide)), Finset.mem_Icc, Finset.mem_map]
    change (-44 ≤ a ∧ a ≤ 44) ↔ ∃ i ∈ Finset.range 89, (i : ℤ)-44 = a
    simp only [Finset.mem_range]
    constructor
    · intro h; exact ⟨(a+44).toNat, by omega, by omega⟩
    · rintro ⟨i,hi,rfl⟩; omega
  rw [he, Finset.sum_map]
  rfl

private theorem eval_cbd (b : ℕ) : (cbd 3).eval b = cbdWord b := by
  simp only [cbd, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, cbdWord, sumTo_eq]
  exact Fin.sum_univ_eq_sum_range (fun a ↦ Nat.choose 6 a * b^((Int.ofNat a-3).natAbs^2)) 7

private theorem eval_cumulative (b : ℕ) (hb : 1 < b) :
    (cumulative 2000).eval b = (b^2001-1)/(b-1) := by
  simp only [cumulative, eval_finsetSum, eval_pow, eval_X]
  apply Nat.eq_div_of_mul_eq_left (by omega)
  exact geom_sum_mul_of_one_le hb.le 2001

-- A power of two exceeding the total mass of either polynomial, including the
-- cumulative factor. Consequently its digits are the exact coefficients.
@[expose] def base := 2^4608
@[expose] def modulus := base^2001
@[expose] def packedBall (d : ℕ) :=
  ((modulus-1)/(base-1) * Nat.powMod (thetaWord base) d modulus) % modulus
@[expose] def packedCBD (d : ℕ) := Nat.powMod (cbdWord base) d modulus

private theorem ball_digit {d k : ℕ} (hd : d ≤ 662) (hk : k ≤ 2000) :
    packedBall d / base^k % base = ballCount d k := by
  rw [← ball_coeff 2000 d k hk]
  apply packed_coeff _ _ _ 2001 (by omega)
  · rw [eval_mul, eval_pow, eval_theta]
    have h1 : thetaWord 1 = 89 := by decide
    rw [h1]
    simp [cumulative, eval_finsetSum]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hd))
      (by decide : 2001 * 89^662 < base)
  · rw [eval_mul, eval_pow, eval_theta, eval_cumulative _ (by decide)]
    unfold packedBall Nat.ModEq
    simp [Nat.powMod_def, modulus]

private theorem cbd_digit {d k : ℕ} (hd : d ≤ 661) (hk : k ≤ 2000) :
    packedCBD d / base^k % base = shell 3 d k := by
  rw [← cbd_coeff]
  apply packed_coeff _ _ _ 2001 (by omega)
  · rw [eval_pow, eval_cbd, show cbdWord 1 = 64 by decide]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hd) (by decide : 64^661 < base)
  · rw [eval_pow, eval_cbd]
    simp [packedCBD, Nat.ModEq, Nat.powMod_def, modulus]

@[expose] def block (h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, c, w => (w % base) * (h - (c % base - 1))
  | a+1, c, w =>
    let split := base^(2^a)
    block h a (c % split) (w % split) + block h a (c / split) (w / split)

@[expose] def fastGain (r : ℕ) := block (2*3329^r) 11 (packedBall (r+513) / base)
  (packedCBD (r+512) % (base^2000))


private def digit (v k : ℕ) := v / base^k % base

private theorem digit_low (v k l : ℕ) (hk : k < l) : digit (v % base^l) k = digit v k := by
  simp only [digit, ← Nat.mod_mul_right_div_self, ← pow_succ,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow base hk)]

private theorem digit_high (v k l : ℕ) : digit (v / base^l) k = digit v (l+k) := by
  simp [digit, pow_add, Nat.div_div_eq_div_mul]

private theorem block_sum (h a c w : ℕ) :
    block h a c w = ∑ k ∈ Finset.range (2^a), digit w k * (h - (digit c k - 1)) := by
  induction a generalizing c w with
  | zero => simp [block, digit]
  | succ a ih =>
    rw [block, pow_succ, Nat.mul_two, Finset.sum_range_add, ih, ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [digit_low _ _ _ (Finset.mem_range.mp hk)]
    · simp only [digit_high]

theorem fastGain_eq (r : ℕ) (hr : r ≤ 149) :
    fastGain r = gain 3 (r+512) r 3329 2000 := by
  rw [fastGain, block_sum, gain]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by decide : 2000 ≤ 2^11))
  · intro k hk
    have h := Finset.mem_sdiff.mp hk
    have hle : 2000 ≤ k := by simpa using h.2
    have hlt : packedCBD (r+512) % base^2000 < base^k :=
      (Nat.mod_lt _ (pow_pos (by decide : 0 < base) _)).trans_le
        (Nat.pow_le_pow_right (by decide) hle)
    simp [digit, Nat.div_eq_of_lt hlt]
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [digit_low _ _ _ h, show packedBall (r+513) / base = packedBall (r+513) / base^1 by rw [pow_one], digit_high]
    unfold digit
    rw [cbd_digit (by omega) (by omega), ball_digit (by omega) (by omega), Nat.add_comm 1 k]

end SigabaNeo.SampleDeletion

#print axioms SigabaNeo.SampleDeletion.cbd_coeff
#print axioms SigabaNeo.SampleDeletion.fastGain_eq
