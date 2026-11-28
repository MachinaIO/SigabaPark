import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option autoImplicit true

/-! # Coefficientwise majorants for finite convolution powers

Every degree-n coefficient uses only degrees at most n. These bounds justify
finite polynomial majorization; they make no factorial-cumulant identification.
-/

namespace SigabaNeo.Wall1.FiniteConvolutionMajorant
open Finset

/-- Ordinary coefficient convolution at one finite degree. -/
def convolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), a i * b (n-i)

/-- Coefficients of the r-th power, with the constant-one series as power zero. -/
def convolutionPower (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | r+1, n => convolution a (convolutionPower a r) n

theorem convolution_nonneg (a b : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N)
    (ha : ∀ i, i ≤ N → 0 ≤ a i) (hb : ∀ i, i ≤ N → 0 ≤ b i) :
    0 ≤ convolution a b n := by
  apply sum_nonneg
  intro i hi
  have hin : i ≤ n := by have := mem_range.mp hi; omega
  exact mul_nonneg (ha i (hin.trans hn)) (hb (n-i) ((Nat.sub_le n i).trans hn))

/-- Absolute coefficient bounds propagate through convolution. The hypotheses
already imply nonnegativity of both majorants on all degrees used here. -/
theorem convolution_abs_le (a b A B : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N)
    (ha : ∀ i, i ≤ N → |a i| ≤ A i) (hb : ∀ i, i ≤ N → |b i| ≤ B i) :
    |convolution a b n| ≤ convolution A B n := by
  unfold convolution
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  have hin : i ≤ n := by have := mem_range.mp hi; omega
  have hai := ha i (hin.trans hn)
  have hbi := hb (n-i) ((Nat.sub_le n i).trans hn)
  rw [abs_mul]
  exact mul_le_mul hai hbi (abs_nonneg _) ((abs_nonneg _).trans hai)

theorem convolutionPower_nonneg (a : ℕ → ℝ) {N : ℕ}
    (ha : ∀ i, i ≤ N → 0 ≤ a i) (r n : ℕ) (hn : n ≤ N) :
    0 ≤ convolutionPower a r n := by
  induction r generalizing n with
  | zero => simp only [convolutionPower]; split_ifs <;> norm_num
  | succ r ih => exact convolution_nonneg a (convolutionPower a r) hn ha ih

/-- The same degree bound suffices for every finite convolution power. -/
theorem convolutionPower_abs_le (a A : ℕ → ℝ) {N : ℕ}
    (ha : ∀ i, i ≤ N → |a i| ≤ A i) (r n : ℕ) (hn : n ≤ N) :
    |convolutionPower a r n| ≤ convolutionPower A r n := by
  induction r generalizing n with
  | zero => simp only [convolutionPower]; split_ifs <;> norm_num
  | succ r ih =>
    exact convolution_abs_le a (convolutionPower a r) A (convolutionPower A r) hn ha ih

/-- Finite exponential coefficient, summing convolution powers through N.
This definition does not assert an identity with an infinite or formal exponential. -/
noncomputable def finiteExp (a : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ r ∈ range (N+1), convolutionPower a r n / (r.factorial : ℝ)

theorem finiteExp_nonneg (a : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N)
    (ha : ∀ i, i ≤ N → 0 ≤ a i) : 0 ≤ finiteExp a N n := by
  apply sum_nonneg
  intro r hr
  exact div_nonneg (convolutionPower_nonneg a ha r n hn) (Nat.cast_nonneg _)

/-- Absolute coefficient bounds pass through the complete finite exponential sum. -/
theorem finiteExp_abs_le (a A : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N)
    (ha : ∀ i, i ≤ N → |a i| ≤ A i) :
    |finiteExp a N n| ≤ finiteExp A N n := by
  unfold finiteExp
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r hr
  rw [abs_div, abs_of_nonneg (show 0 ≤ (r.factorial : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (convolutionPower_abs_le a A ha r n hn)
    (Nat.cast_nonneg _)

/-- At positive degree, the constant-one convolution power contributes zero. -/
theorem finiteExp_positive_degree (a : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    finiteExp a N n =
      ∑ r ∈ range N, convolutionPower a (r+1) n / ((r+1).factorial : ℝ) := by
  have hz : convolutionPower a 0 n = 0 := by simp [convolutionPower, Nat.ne_of_gt hn]
  rw [finiteExp, sum_range_succ']
  simp only [hz, zero_div, add_zero]

end SigabaNeo.Wall1.FiniteConvolutionMajorant

#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.convolution_nonneg
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.convolution_abs_le
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.convolutionPower_nonneg
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.convolutionPower_abs_le
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.finiteExp_nonneg
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.finiteExp_abs_le
#print axioms SigabaNeo.Wall1.FiniteConvolutionMajorant.finiteExp_positive_degree
