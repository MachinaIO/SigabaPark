import Definitions.Def_LatticeAttack_Research_Wall1_FactorialMomentTransfer
import Mathlib.RingTheory.Polynomial.Pochhammer

set_option autoImplicit true

/-! # The concrete normalized kernel used by the raw void certificate

These are the untilted coefficients of wall1_affine_square_certificate.py.
The normalization and reference denominator are proved here; the actual
mean lower bound and the dependent-design correction remain separate inputs.
-/

noncomputable section
namespace SigabaNeo.Wall1.CharlierVoidKernel
open Finset Polynomial

def partialExp (t : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ range (t+1), μ^j / (j.factorial : ℝ)

def coefficient (t : ℕ) (μ : ℝ) (j : ℕ) : ℝ :=
  (-1)^j * partialExp (t-j) μ / (j.factorial : ℝ)

def kernel (t : ℕ) (μ x : ℝ) : ℝ :=
  ∑ j ∈ range (t+1), coefficient t μ j * (descPochhammer ℝ j).eval x

def normalizedKernel (t : ℕ) (μ x : ℝ) : ℝ := kernel t μ x / partialExp t μ

theorem one_le_partialExp (t : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    1 ≤ partialExp t μ := by
  have h := single_le_sum (fun j (_ : j ∈ range (t+1)) ↦
    div_nonneg (pow_nonneg hμ j) (Nat.cast_nonneg j.factorial))
    (show 0 ∈ range (t+1) by simp)
  simpa only [partialExp, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using h

theorem partialExp_mono (t : ℕ) {μ ν : ℝ} (hμ : 0 ≤ μ) (h : μ ≤ ν) :
    partialExp t μ ≤ partialExp t ν := by
  apply sum_le_sum
  intro j hj
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hμ h j) (Nat.cast_nonneg _)

theorem kernel_zero (t : ℕ) (μ : ℝ) : kernel t μ 0 = partialExp t μ := by
  simp [kernel, descPochhammer_eval_zero, mul_ite, coefficient]

theorem normalizedKernel_zero (t : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    normalizedKernel t μ 0 = 1 := by
  have hp : 0 < partialExp t μ := lt_of_lt_of_le (by norm_num) (one_le_partialExp t hμ)
  rw [normalizedKernel, kernel_zero, div_self hp.ne']

/-- Agreement with the falling-factorial coefficient convention for integer counts. -/
theorem kernel_nat (t : ℕ) (μ : ℝ) (z : ℕ) :
    kernel t μ z = ∑ j ∈ range (t+1), coefficient t μ j * (z.descFactorial j : ℝ) := by
  simp only [kernel, descPochhammer_eval_eq_descFactorial]

/-- The reference part of the exit bound, conditional on the actual mean lower bound. -/
theorem degree12_reference_bound {μ : ℝ} (hμ : 58.5115 ≤ μ) :
    1 / ((7 / 25) * partialExp 12 μ) < (849 / 1000000000000000 : ℝ) := by
  have hlo : (4206800000000 : ℝ) ≤ partialExp 12 58.5115 := by
    norm_num [partialExp, sum_range_succ, Nat.factorial]
  have hd := hlo.trans (partialExp_mono 12 (by norm_num) hμ)
  have hp : 0 < (7 / 25 : ℝ) * partialExp 12 μ := by nlinarith
  apply (div_lt_iff₀ hp).2
  nlinarith

/-- Sharper rational rounding for adding the separately bounded correction term. -/
theorem degree12_reference_bound_sharp {μ : ℝ} (hμ : 58.5115 ≤ μ) :
    1 / ((7 / 25) * partialExp 12 μ) < (84896 / 100000000000000000 : ℝ) := by
  have hlo : (4206830000000 : ℝ) ≤ partialExp 12 58.5115 := by
    norm_num [partialExp, sum_range_succ, Nat.factorial]
  have hd := hlo.trans (partialExp_mono 12 (by norm_num) hμ)
  have hp : 0 < (7 / 25 : ℝ) * partialExp 12 μ := by nlinarith
  apply (div_lt_iff₀ hp).2
  nlinarith

open ControlledPlane TerminalProjection RawPrefixOccupancy CenteredPrefixOccupancy
open SquareVoidCertificate

/-- The concrete degree12 kernel bounds the actual gated history, for any
nonnegative deterministic parameter. Sharp numerical estimates require its
parameter to be matched to the actual raw mean by a separate proof. -/
theorem actual_slack_exit_le_degree12 {μ : ℝ} (hμ : 0 ≤ μ) :
    ((7 * Fintype.card Column *
      (gatedExitSet
        (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
        (fun i A ↦ actualSlackRadius A (entry i))).card : ℕ) : ℝ) ≤
    25 * ∑ A, ∑ c, normalizedKernel 12 μ
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A c) ^ 2 := by
  exact actual_slack_exit_le_square (normalizedKernel 12 μ) (normalizedKernel_zero 12 hμ)

end SigabaNeo.Wall1.CharlierVoidKernel

#print axioms SigabaNeo.Wall1.CharlierVoidKernel.normalizedKernel_zero
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.kernel_nat
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.degree12_reference_bound
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.actual_slack_exit_le_degree12
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.degree12_reference_bound_sharp
