import Definitions.Def_LatticeAttack_Research_Wall1_ActualSlackHistory

set_option autoImplicit true

/-! # Square certificates for the remaining raw void sum

A function equal to one at zero yields a pointwise square majorant. The
polynomial identity exposes the moments through degree twice its degree.
No Poisson approximation or numerical moment bounds are assumed here.
-/

noncomputable section
namespace SigabaNeo.Wall1.SquareVoidCertificate
open Finset CosetOccupancy
open scoped Classical

theorem emptyCount_le_square {α : Type*} [Fintype α] (n : α → ℕ)
    (Q : ℝ → ℝ) (hQ : Q 0 = 1) :
    (emptyCount n : ℝ) ≤ ∑ c, Q (n c) ^ 2 := by
  have hid : (emptyCount n : ℝ) = ∑ c, if n c = 0 then (1 : ℝ) else 0 := by
    simp [emptyCount, sum_boole]
  rw [hid]
  apply sum_le_sum
  intro c hc
  by_cases h : n c = 0
  · simp [h, hQ]
  · simp only [h, ite_false]
    exact sq_nonneg _

theorem total_emptyCount_le_square {Ω α : Type*} [Fintype Ω] [Fintype α]
    (n : Ω → α → ℕ) (Q : ℝ → ℝ) (hQ : Q 0 = 1) :
    ((∑ ω, emptyCount (n ω) : ℕ) : ℝ) ≤ ∑ ω, ∑ c, Q (n ω c) ^ 2 := by
  push_cast
  exact sum_le_sum fun ω _ ↦ emptyCount_le_square (n ω) Q hQ

/-- A degree-t square uses raw moments only through degree 2t, with exact signs. -/
theorem polynomial_square_moments {Ω α : Type*} [Fintype Ω] [Fintype α]
    (n : Ω → α → ℕ) (J : Finset ℕ) (a : ℕ → ℝ) :
    (∑ ω, ∑ c, (∑ j ∈ J, a j * (n ω c : ℝ)^j)^2) =
      ∑ i ∈ J, ∑ j ∈ J, a i * a j * ∑ ω, ∑ c, (n ω c : ℝ)^(i+j) := by
  have expand (x : ℝ) : (∑ j ∈ J, a j * x^j)^2 =
      ∑ i ∈ J, ∑ j ∈ J, (a i * a j) * x^(i+j) := by
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  simp_rw [expand, mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext c; rw [sum_comm]; arg 2; ext i; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]

open ControlledPlane TerminalProjection RawPrefixOccupancy CenteredPrefixOccupancy

/-- The actual gated exit count is bounded by any normalized raw square certificate.
The right side must still be evaluated under the original full matrix law. -/
theorem actual_slack_exit_le_square (Q : ℝ → ℝ) (hQ : Q 0 = 1) :
    ((7 * Fintype.card Column *
      (gatedExitSet
        (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
        (fun i A ↦ actualSlackRadius A (entry i))).card : ℕ) : ℝ) ≤
    25 * ∑ A, ∑ c, Q
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A c) ^ 2 := by
  have h := (Nat.cast_le (α := ℝ)).mpr actual_slack_history_exit_first_moment
  refine h.trans ?_
  push_cast
  have hm := total_emptyCount_le_square
    (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius)) Q hQ
  push_cast at hm
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

/-- Exact raw-power-moment reduction for a chosen normalized polynomial.
Signed coefficients are retained; termwise upper bounds cannot be substituted
without accounting for their signs. -/
theorem actual_slack_exit_le_polynomial_moments (J : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∑ j ∈ J, a j * (0 : ℝ)^j = 1) :
    ((7 * Fintype.card Column *
      (gatedExitSet
        (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
        (fun i A ↦ actualSlackRadius A (entry i))).card : ℕ) : ℝ) ≤
    25 * ∑ i ∈ J, ∑ j ∈ J, a i * a j * ∑ A, ∑ c,
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A c : ℝ)^(i+j) := by
  have h := actual_slack_exit_le_square (fun x ↦ ∑ j ∈ J, a j * x^j) ha
  rw [polynomial_square_moments] at h
  exact h

end SigabaNeo.Wall1.SquareVoidCertificate

#print axioms SigabaNeo.Wall1.SquareVoidCertificate.total_emptyCount_le_square
#print axioms SigabaNeo.Wall1.SquareVoidCertificate.polynomial_square_moments
#print axioms SigabaNeo.Wall1.SquareVoidCertificate.actual_slack_exit_le_square
#print axioms SigabaNeo.Wall1.SquareVoidCertificate.actual_slack_exit_le_polynomial_moments
