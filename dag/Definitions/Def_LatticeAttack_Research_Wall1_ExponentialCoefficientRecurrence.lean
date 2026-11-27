import Mathlib.Tactic

set_option autoImplicit true

/-! Finite exponential coefficient recurrence and coefficientwise majorization.
The actual moment/cumulant identification is a separate theorem. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open Finset

def exponentialCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if hn : n = 0 then 1 else
    (∑ i : Fin n, (i.val+1 : ℕ) * a (i.val+1) *
      exponentialCoefficient a (n-1-i.val)) / (n : ℝ)
termination_by n

theorem exponentialCoefficient_zero (a : ℕ → ℝ) : exponentialCoefficient a 0 = 1 := by
  rw [exponentialCoefficient]
  simp

theorem exponentialCoefficient_pos (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    exponentialCoefficient a n =
      (∑ i : Fin n, (i.val+1 : ℕ) * a (i.val+1) *
        exponentialCoefficient a (n-1-i.val)) / (n : ℝ) := by
  rw [exponentialCoefficient, dif_neg (Nat.ne_of_gt hn)]

/-- The recurrence determines all coefficients from the constant term. -/
theorem exponentialCoefficient_unique (a d : ℕ → ℝ) (hzero : d 0 = 1)
    (hrec : ∀ n, 0 < n → d n =
      (∑ i : Fin n, (i.val+1 : ℕ) * a (i.val+1) * d (n-1-i.val)) / (n : ℝ)) :
    ∀ n, exponentialCoefficient a n = d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rw [exponentialCoefficient_zero, hzero]
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      rw [exponentialCoefficient_pos a hp, hrec n hp]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [ih (n-1-i.val) (by omega)]

/-- Absolute input bounds propagate through the finite exponential recurrence. -/
theorem exponentialCoefficient_abs_le (a A : ℕ → ℝ) {N : ℕ}
    (ha : ∀ j, 1 ≤ j → j ≤ N → |a j| ≤ A j) :
    ∀ n, n ≤ N → |exponentialCoefficient a n| ≤ exponentialCoefficient A n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hnN
    by_cases hn : n = 0
    · subst n
      simp [exponentialCoefficient_zero]
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      rw [exponentialCoefficient_pos a hp, exponentialCoefficient_pos A hp,
        abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
      apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (i.val+1:ℕ) from Nat.cast_nonneg _)]
      have hj := ha (i.val+1) (by omega) (by omega)
      have hi := ih (n-1-i.val) (by omega) (by omega)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _)) hi
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans hj))

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.exponentialCoefficient_unique
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.exponentialCoefficient_abs_le
