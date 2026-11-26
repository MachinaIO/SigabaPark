import Definitions.Def_LatticeAttack_Research_Wall1_FormalLogAdditivity

set_option autoImplicit true

/-! A cubic joint-law defect has an exact linear source in its log-derivative equation. -/
noncomputable section
namespace SigabaNeo.Wall1.CubicLogDefect
open PowerSeries ExponentialCoefficientRecurrence

def baseline (a b c : ℝ) : PowerSeries ℝ := 1 + C a * X + C b * X^2 + C c * X^3

def perturbed (a b c d : ℝ) : PowerSeries ℝ := baseline a b c + C d * X^3

def logDefect (a b c d : ℝ) : PowerSeries ℝ :=
  logOf (perturbed a b c d) - logOf (baseline a b c)

theorem baseline_constant (a b c : ℝ) : constantCoeff (baseline a b c) = 1 := by
  simp [baseline]

theorem perturbed_constant (a b c d : ℝ) : constantCoeff (perturbed a b c d) = 1 := by
  simp [perturbed, baseline_constant]

theorem derivative_baseline (a b c : ℝ) :
    derivative (baseline a b c) = C a + C (2*b)*X + C (3*c)*X^2 := by
  simp [baseline, map_add, Derivation.leibniz, smul_eq_mul, map_mul, map_ofNat]
  ring

/-- Multiplying by the two generating polynomials leaves a source linear in d.
This identity is exact and makes no smallness assumption on the probabilities. -/
theorem logDefect_derivative_identity (a b c d : ℝ) :
    derivative (logDefect a b c d) *
        (baseline a b c * perturbed a b c d) =
      C d * X^2 * (C 3 + C (2*a)*X + C b * X^2) := by
  have hf := derivative_logOf_mul (perturbed a b c d) (perturbed_constant a b c d)
  have hp := derivative_logOf_mul (baseline a b c) (baseline_constant a b c)
  have he : derivative (logDefect a b c d) *
      (baseline a b c * perturbed a b c d) =
      derivative (perturbed a b c d) * baseline a b c -
        derivative (baseline a b c) * perturbed a b c d := by
    unfold logDefect
    rw [map_sub]
    calc
      _ = (derivative (logOf (perturbed a b c d))*perturbed a b c d)*baseline a b c -
          (derivative (logOf (baseline a b c))*baseline a b c)*perturbed a b c d := by ring
      _ = _ := by rw [hf,hp]
  rw [he]
  simp [perturbed, baseline, map_add, Derivation.leibniz, smul_eq_mul, map_mul, map_ofNat]
  ring

/-- A finite triangular recurrence for every higher coefficient, with no
division by a formal series and no convergence hypothesis. -/
theorem logDefect_coefficient_recurrence (a b c d : ℝ) (n : ℕ) :
    (n+1 : ℝ) * coeff (n+1) (logDefect a b c d) =
      coeff n (C d * X^2 * (C 3 + C (2*a)*X + C b * X^2)) -
        ∑ i ∈ Finset.range n,
          ((i+1 : ℝ) * coeff (i+1) (logDefect a b c d)) *
            coeff (n-i) (baseline a b c * perturbed a b c d) := by
  have h := congrArg (coeff n) (logDefect_derivative_identity a b c d)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at h
  simp only [coeff_derivative, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    map_mul, baseline_constant, perturbed_constant, mul_one] at h
  have hsum : (∑ i ∈ Finset.range n,
      coeff (i+1) (logDefect a b c d) * (i+1 : ℝ) *
        coeff (n-i) (baseline a b c * perturbed a b c d)) =
      ∑ i ∈ Finset.range n,
      ((i+1 : ℝ) * coeff (i+1) (logDefect a b c d)) *
        coeff (n-i) (baseline a b c * perturbed a b c d) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at h
  simp only [map_mul]
  linarith

theorem bernoulli_baseline (p q r : ℝ) :
    baseline (p+q+r) (p*q+p*r+q*r) (p*q*r) =
      (1+C p*X)*(1+C q*X)*(1+C r*X) := by
  simp only [baseline, map_add, map_mul]
  ring

theorem logDefect_eq_triple_correction (p q r d : ℝ) :
    logDefect (p+q+r) (p*q+p*r+q*r) (p*q*r) d =
      logOf (perturbed (p+q+r) (p*q+p*r+q*r) (p*q*r) d) -
        (logOf (1+C p*X) + logOf (1+C q*X) + logOf (1+C r*X)) := by
  unfold logDefect
  rw [bernoulli_baseline,
    logOf_mul_normalized _ _ (by simp) (by simp),
    logOf_mul_normalized _ _ (by simp) (by simp)]

end SigabaNeo.Wall1.CubicLogDefect
#print axioms SigabaNeo.Wall1.CubicLogDefect.logDefect_derivative_identity
#print axioms SigabaNeo.Wall1.CubicLogDefect.logDefect_coefficient_recurrence
#print axioms SigabaNeo.Wall1.CubicLogDefect.logDefect_eq_triple_correction
