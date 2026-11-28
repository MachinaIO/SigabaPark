import Definitions.Def_LatticeAttack_Research_Wall1_CharlierSquare

set_option autoImplicit true

/-! # Exact reference functional for the degree12 kernel

These finite polynomial identities evaluate the functional (x)_h ↦ mu^h.
They do not identify the actual raw count with a Poisson random variable.
-/

noncomputable section
namespace SigabaNeo.Wall1.CharlierVoidKernel
open Finset Polynomial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem reference_falling12 (μ : ℝ) (i : ℕ) (hi : i ≤ 12) :
    (∑ j ∈ range 13, ∑ l ∈ range (min i j + 1),
      coefficient 12 μ j *
        ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) *
          μ^(i+j-l)) = if i = 0 then 1 else 0 := by
  interval_cases i <;>
    norm_num [coefficient, partialExp, sum_range_succ, Nat.choose, Nat.factorial] <;> ring

theorem reference_square12 (μ : ℝ) :
    (∑ h ∈ range 25, squareCoefficient μ h * μ^h) = partialExp 12 μ := by
  calc
    _ = ∑ i ∈ range 13, coefficient 12 μ i *
        (∑ j ∈ range 13, ∑ l ∈ range (min i j + 1),
          coefficient 12 μ j *
            ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) *
              μ^(i+j-l)) := by
      simp only [squareCoefficient, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro l hl
      have hd : i+j-l ∈ range 25 := mem_range.mpr (by
        have := square_term_degree_le (l := l) hi hj
        omega)
      simp only [ite_mul, zero_mul, sum_ite_eq, ite_eq_left hd]
      ring
    _ = ∑ i ∈ range 13, coefficient 12 μ i * (if i = 0 then 1 else 0) := by
      apply sum_congr rfl
      intro i hi
      rw [reference_falling12 μ i (by have := mem_range.mp hi; omega)]
    _ = _ := by simp [coefficient]

open FactorialMomentTransfer

theorem normalized_reference_weight12 {μ : ℝ} (hμ : 0 ≤ μ) :
    differenceWeight (range 25) (fun h ↦ squareCoefficient μ h / partialExp 12 μ ^ 2) μ 0 =
      1 / partialExp 12 μ := by
  have hp : partialExp 12 μ ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_partialExp 12 hμ)).ne'
  have hzero (h : ℕ) : transferCoefficient μ h 0 = μ^h := by
    simp [transferCoefficient, Nat.factorial_ne_zero]
  simp only [differenceWeight, hzero, div_mul_eq_mul_div, ← sum_div]
  rw [reference_square12]
  field_simp

end SigabaNeo.Wall1.CharlierVoidKernel
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.reference_falling12

#print axioms SigabaNeo.Wall1.CharlierVoidKernel.reference_square12
#print axioms SigabaNeo.Wall1.CharlierVoidKernel.normalized_reference_weight12
