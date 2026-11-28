import Definitions.Def_LatticeAttack_Research_Wall1_FiniteExponentialRecurrence
import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalLogCoefficients

set_option autoImplicit true

/-! Exact reconstruction by a finite exponential sum through its truncation degree.
No analytic convergence or moment interpretation is required. -/
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open Finset FiniteConvolutionMajorant

/-- The recursive exponential coefficients equal the truncated convolution exponential. -/
theorem exponentialCoefficient_eq_finiteExp (a : ℕ → ℝ) (ha : a 0 = 0)
    {N n : ℕ} (hn : n ≤ N) :
    exponentialCoefficient a n = finiteExp a N n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [exponentialCoefficient_zero, finiteExp_zero a ha]
    | succ n =>
      rw [exponentialCoefficient_pos a (by omega)]
      simp only [Nat.add_sub_cancel]
      have hrec := finiteExp_succ_recurrence a ha hn
      have hnonzero : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
      apply (div_eq_iff hnonzero).mpr
      rw [mul_comm, hrec, ← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i _
      rw [ih (n-i.val) (by omega) (by omega)]

/-- A normalized sequence is exactly recovered from its triangular logarithmic coefficients. -/
theorem finiteExp_logarithmicCoefficient (d : ℕ → ℝ) (hzero : d 0 = 1)
    (N n : ℕ) (hn : n ≤ N) :
    finiteExp (logarithmicCoefficient d) N n = d n := by
  rw [← exponentialCoefficient_eq_finiteExp _ (logarithmicCoefficient_zero d) hn]
  exact exponential_logarithmicCoefficient d hzero n

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence

#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.exponentialCoefficient_eq_finiteExp
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.finiteExp_logarithmicCoefficient
