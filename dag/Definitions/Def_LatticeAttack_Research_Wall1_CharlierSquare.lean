import Definitions.Def_LatticeAttack_Research_Wall1_CharlierVoidKernel
import Definitions.Def_LatticeAttack_Research_Wall1_DescFactorialProduct12

set_option autoImplicit true

/-! # Exact degree12 kernel square in the falling-factorial basis

The triple sum is exactly the contribution loop in the Python coefficient
generator, before collecting contributions with equal factorial degree.
-/

noncomputable section
namespace SigabaNeo.Wall1.CharlierVoidKernel
open Finset Polynomial

theorem kernel12_square (μ x : ℝ) :
    kernel 12 μ x ^ 2 =
    ∑ i ∈ range 13, ∑ j ∈ range 13, ∑ l ∈ range (min i j + 1),
      (coefficient 12 μ i * coefficient 12 μ j) *
        ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) *
        (descPochhammer ℝ (i+j-l)).eval x := by
  rw [kernel, pow_two, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hi' : i ≤ 12 := by have := mem_range.mp hi; omega
  have hj' : j ≤ 12 := by have := mem_range.mp hj; omega
  calc
    _ = (coefficient 12 μ i * coefficient 12 μ j) *
        ((descPochhammer ℝ i).eval x * (descPochhammer ℝ j).eval x) := by ring
    _ = _ := by
      rw [desc_product_bounded i j hi' hj', mul_sum]
      apply sum_congr rfl
      intro l hl
      ring

theorem kernel12_square_nat (μ : ℝ) (z : ℕ) :
    kernel 12 μ z ^ 2 =
    ∑ i ∈ range 13, ∑ j ∈ range 13, ∑ l ∈ range (min i j + 1),
      (coefficient 12 μ i * coefficient 12 μ j) *
        ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) *
        (z.descFactorial (i+j-l) : ℝ) := by
  simpa only [descPochhammer_eval_eq_descFactorial] using kernel12_square μ z

theorem square_term_degree_le {i j l : ℕ} (hi : i ∈ range 13) (hj : j ∈ range 13) :
    i+j-l ≤ 24 := by
  have := mem_range.mp hi
  have := mem_range.mp hj
  omega

/-- Collected falling-factorial coefficient, matching the untilted Python loop. -/
def squareCoefficient (μ : ℝ) (h : ℕ) : ℝ :=
  ∑ i ∈ range 13, ∑ j ∈ range 13, ∑ l ∈ range (min i j + 1),
    if i+j-l = h then (coefficient 12 μ i * coefficient 12 μ j) *
      ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) else 0

theorem kernel12_square_collected (μ x : ℝ) :
    kernel 12 μ x ^ 2 =
      ∑ h ∈ range 25, squareCoefficient μ h * (descPochhammer ℝ h).eval x := by
  rw [kernel12_square]
  symm
  simp only [squareCoefficient, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  have hd : i+j-l ∈ range 25 := mem_range.mpr (by have := square_term_degree_le (l := l) hi hj; omega)
  simp only [ite_mul, zero_mul, sum_ite_eq, ite_eq_left hd]

theorem kernel12_square_collected_nat (μ : ℝ) (z : ℕ) :
    kernel 12 μ z ^ 2 =
      ∑ h ∈ range 25, squareCoefficient μ h * (z.descFactorial h : ℝ) := by
  simpa only [descPochhammer_eval_eq_descFactorial] using kernel12_square_collected μ z

theorem normalizedKernel12_square_collected (μ : ℝ) (z : ℕ) :
    normalizedKernel 12 μ z ^ 2 =
      ∑ h ∈ range 25, (squareCoefficient μ h / partialExp 12 μ ^ 2) *
        (z.descFactorial h : ℝ) := by
  rw [normalizedKernel, div_pow, kernel12_square_collected_nat, sum_div]
  apply sum_congr rfl
  intro h hh
  ring

end SigabaNeo.Wall1.CharlierVoidKernel

#print axioms SigabaNeo.Wall1.CharlierVoidKernel.kernel12_square
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.kernel12_square_nat
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.kernel12_square_collected
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.normalizedKernel12_square_collected
