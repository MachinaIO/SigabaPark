import Definitions.Def_LatticeAttack_Research_Wall1_SquareVoidCertificate

set_option autoImplicit true

/-! # Finite factorial-moment transfer with signed coefficients

This is a finite triangular identity and an absolute-error bound. It does not
assume that an actual count has a Poisson law, or assert the geometric bounds
on its factorial moments or connected-incidence corrections.
-/

noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset
open scoped Classical

/-- Coefficient in the finite convolution F_h=h! sum_k d_k mu^(h-k)/(h-k)!. -/
def transferCoefficient (μ : ℝ) (h k : ℕ) : ℝ :=
  if k ≤ h then μ^(h-k) * (h.factorial : ℝ) / ((h-k).factorial : ℝ) else 0

/-- Finite-difference weight of a polynomial given in the falling-factorial basis. -/
def differenceWeight (J : Finset ℕ) (f : ℕ → ℝ) (μ : ℝ) (k : ℕ) : ℝ :=
  ∑ h ∈ J, f h * transferCoefficient μ h k

/-- Exact finite transfer. The convolution identity is an explicit input. -/
theorem finite_transfer (J : Finset ℕ) (f F d : ℕ → ℝ) (μ : ℝ)
    (hF : ∀ h ∈ J, F h = ∑ k ∈ J, d k * transferCoefficient μ h k) :
    ∑ h ∈ J, f h * F h = ∑ k ∈ J, differenceWeight J f μ k * d k := by
  calc
    _ = ∑ h ∈ J, ∑ k ∈ J, f h * (d k * transferCoefficient μ h k) := by
      apply sum_congr rfl
      intro h hh
      rw [hF h hh, mul_sum]
    _ = ∑ k ∈ J, ∑ h ∈ J, f h * (d k * transferCoefficient μ h k) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [differenceWeight, sum_mul]
      apply sum_congr rfl
      intro h hh
      ring

/-- Signed weights are bounded against absolute errors, not against one-sided moments. -/
theorem weighted_error_upper {ι : Type*} (J : Finset ι) (w d b E : ι → ℝ)
    (herr : ∀ k ∈ J, |d k - b k| ≤ E k) :
    ∑ k ∈ J, w k * d k ≤
      (∑ k ∈ J, w k * b k) + ∑ k ∈ J, |w k| * E k := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  have h : w k * (d k - b k) ≤ |w k| * E k := calc
    _ ≤ |w k * (d k - b k)| := le_abs_self _
    _ = |w k| * |d k - b k| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (herr k hk) (abs_nonneg _)
  linarith

/-- Poisson-reference transfer with explicit correction errors. Setting E_0=E_1=0
is justified only after the constant and first-moment identities are established. -/
theorem finite_transfer_upper (J : Finset ℕ) (hzero : 0 ∈ J)
    (f F d E : ℕ → ℝ) (μ : ℝ)
    (hF : ∀ h ∈ J, F h = ∑ k ∈ J, d k * transferCoefficient μ h k)
    (herr : ∀ k ∈ J, |d k - (if k = 0 then 1 else 0)| ≤ E k) :
    ∑ h ∈ J, f h * F h ≤ differenceWeight J f μ 0 +
      ∑ k ∈ J, |differenceWeight J f μ k| * E k := by
  rw [finite_transfer J f F d μ hF]
  have h := weighted_error_upper J (differenceWeight J f μ) d
    (fun k ↦ if k = 0 then 1 else 0) E herr
  simpa only [mul_ite, mul_one, mul_zero, sum_ite_eq', ite_eq_left hzero] using h

/-- Joint uniform factorial moment over matrices and independent raw labels. -/
def factorialAverage {Ω α : Type*} [Fintype Ω] [Fintype α]
    (n : Ω → α → ℕ) (j : ℕ) : ℝ :=
  (∑ ω, ∑ c, ((n ω c).descFactorial j : ℝ)) /
    ((Fintype.card Ω : ℝ) * Fintype.card α)

/-- Zeroth factorial moment of a nonempty joint uniform sample space. -/
theorem factorialAverage_zero {Ω α : Type*} [Fintype Ω] [Fintype α]
    [Nonempty Ω] [Nonempty α] (n : Ω → α → ℕ) : factorialAverage n 0 = 1 := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [factorialAverage, Nat.descFactorial_zero, Nat.cast_one, sum_const,
    card_univ, nsmul_eq_mul, mul_one, div_self (mul_ne_zero hΩ hα)]

/-- A falling-factorial expansion transfers exactly to the normalized joint average. -/
theorem square_average_eq {Ω α : Type*} [Fintype Ω] [Fintype α]
    (n : Ω → α → ℕ) (Q : ℝ → ℝ) (J : Finset ℕ) (f : ℕ → ℝ)
    (hQ : ∀ z : ℕ, Q z ^ 2 = ∑ j ∈ J, f j * (z.descFactorial j : ℝ)) :
    (∑ ω, ∑ c, Q (n ω c) ^ 2) /
      ((Fintype.card Ω : ℝ) * Fintype.card α) =
    ∑ j ∈ J, f j * factorialAverage n j := by
  simp_rw [hQ]
  conv_lhs => arg 1; arg 2; ext ω; rw [sum_comm]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro j hj
  simp only [factorialAverage, ← mul_sum, mul_div_assoc]

/-- Safe error transfer for the actual normalized square average. The input
identities and correction bounds must concern this very joint law. -/
theorem square_average_le_transfer {Ω α : Type*} [Fintype Ω] [Fintype α]
    (n : Ω → α → ℕ) (Q : ℝ → ℝ) (J : Finset ℕ) (hzero : 0 ∈ J)
    (f d E : ℕ → ℝ) (μ : ℝ)
    (hQ : ∀ z : ℕ, Q z ^ 2 = ∑ j ∈ J, f j * (z.descFactorial j : ℝ))
    (hF : ∀ h ∈ J, factorialAverage n h = ∑ k ∈ J, d k * transferCoefficient μ h k)
    (herr : ∀ k ∈ J, |d k - (if k = 0 then 1 else 0)| ≤ E k) :
    (∑ ω, ∑ c, Q (n ω c) ^ 2) /
      ((Fintype.card Ω : ℝ) * Fintype.card α) ≤
    differenceWeight J f μ 0 + ∑ k ∈ J, |differenceWeight J f μ k| * E k := by
  rw [square_average_eq n Q J f hQ]
  exact finite_transfer_upper J hzero f (factorialAverage n) d E μ hF herr

end SigabaNeo.Wall1.FactorialMomentTransfer

#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.finite_transfer
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.finite_transfer_upper
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.square_average_le_transfer
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.factorialAverage_zero
