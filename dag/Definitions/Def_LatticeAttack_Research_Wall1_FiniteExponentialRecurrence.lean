import Definitions.Def_LatticeAttack_Research_Wall1_FiniteConvolutionMajorant
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit true

/-! Finite exponential coefficients and their exact logarithmic-derivative recurrence. -/
namespace SigabaNeo.Wall1.FiniteConvolutionMajorant
open Finset

lemma convolutionPower_eq_coeff (a : ℕ → ℝ) (r n : ℕ) :
    convolutionPower a r n = PowerSeries.coeff n ((PowerSeries.mk a)^r) := by
  induction r generalizing n with
  | zero => simp [convolutionPower, PowerSeries.coeff_one]
  | succ r ih =>
    rw [convolutionPower, pow_succ', PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [convolution, PowerSeries.coeff_mk, ih]

lemma convolutionPower_eq_zero_of_lt (a : ℕ → ℝ) (ha : a 0 = 0)
    {r n : ℕ} (hn : n < r) : convolutionPower a r n = 0 := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
    unfold convolutionPower convolution
    apply sum_eq_zero
    intro i hi
    have hin := mem_range.mp hi
    by_cases hz : i = 0
    · simp [hz, ha]
    · rw [ih (by omega), mul_zero]

lemma finiteExp_zero (a : ℕ → ℝ) (ha : a 0 = 0) (N : ℕ) :
    finiteExp a N 0 = 1 := by
  unfold finiteExp
  rw [sum_range_succ']
  have hz : ∀ r ∈ range N, convolutionPower a (r+1) 0 / ((r+1).factorial : ℝ) = 0 := by
    intro r _
    rw [convolutionPower_eq_zero_of_lt a ha (by omega), zero_div]
  rw [sum_eq_zero hz]
  simp [convolutionPower]

lemma finiteExp_succ_eq (a : ℕ → ℝ) (ha : a 0 = 0) {N n : ℕ} (hn : n ≤ N) :
    finiteExp a (N+1) n = finiteExp a N n := by
  rw [finiteExp, sum_range_succ]
  rw [convolutionPower_eq_zero_of_lt a ha (by omega), zero_div, add_zero]
  rfl

/-- The differentiated power identity, before dividing by factorials. -/
lemma convolutionPower_succ_recurrence (a : ℕ → ℝ) (r n : ℕ) :
    ((n+1 : ℕ) : ℝ) * convolutionPower a (r+1) (n+1) =
      ((r+1 : ℕ) : ℝ) *
        ∑ i ∈ range (n+1), ((i+1 : ℕ) : ℝ) * a (i+1) * convolutionPower a r (n-i) := by
  have h := congrArg (PowerSeries.coeff n)
    (PowerSeries.derivative_pow (PowerSeries.mk a) (r+1))
  rw [PowerSeries.coeff_derivative, Nat.add_sub_cancel] at h
  rw [mul_comm ((r+1 : ℕ) : PowerSeries ℝ), mul_assoc,
    mul_comm ((r+1 : ℕ) : PowerSeries ℝ), ← mul_assoc] at h
  simp only [PowerSeries.coeff_mul_natCast] at h
  rw [mul_comm ((PowerSeries.mk a)^r), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    ← convolutionPower_eq_coeff, Nat.cast_add, Nat.cast_one] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact recurrence, with the positive index represented as `i+1`. -/
theorem finiteExp_succ_recurrence (a : ℕ → ℝ) (ha : a 0 = 0)
    {N n : ℕ} (hn : n+1 ≤ N) :
    ((n+1 : ℕ) : ℝ) * finiteExp a N (n+1) =
      ∑ i ∈ range (n+1), ((i+1 : ℕ) : ℝ) * a (i+1) * finiteExp a N (n-i) := by
  cases N with
  | zero => omega
  | succ N =>
    have hcoeff (r : ℕ) :
        ((n+1 : ℕ) : ℝ) *
            (convolutionPower a (r+1) (n+1) / ((r+1).factorial : ℝ)) =
          ∑ i ∈ range (n+1), ((i+1 : ℕ) : ℝ) * a (i+1) *
            (convolutionPower a r (n-i) / (r.factorial : ℝ)) := by
      rw [← mul_div_assoc, convolutionPower_succ_recurrence,
        Nat.factorial_succ, Nat.cast_mul]
      simp_rw [← mul_div_assoc]
      rw [← sum_div]
      have hr : ((r+1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [finiteExp_positive_degree a (N+1) (by omega), mul_sum]
    simp_rw [hcoeff]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [← mul_sum, ← finiteExp]
    rw [finiteExp_succ_eq a ha (by omega : n-i ≤ N)]

/-- The usual logarithmic-derivative recurrence at any degree through the truncation. -/
theorem finiteExp_recurrence (a : ℕ → ℝ) (ha : a 0 = 0)
    {N n : ℕ} (hn : n ≤ N) :
    (n : ℝ) * finiteExp a N n =
      ∑ j ∈ range (n+1), (j : ℝ) * a j * finiteExp a N (n-j) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]
    convert finiteExp_succ_recurrence a ha hn using 1
    apply sum_congr rfl
    intro i _
    rw [Nat.add_sub_add_right]

end SigabaNeo.Wall1.FiniteConvolutionMajorant
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.convolutionPower_succ_recurrence

#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.finiteExp_zero
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.finiteExp_recurrence
