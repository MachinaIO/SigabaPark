module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

/-- A finite-horizon drift budget, also applicable to sequences of expectations. -/
theorem driftBudget (P loss : ℕ → ℝ) (T : ℕ)
    (step : ∀ t < T, loss t ≤ P t - P (t + 1)) :
    ∑ t ∈ Finset.range T, loss t ≤ P 0 - P T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h := ih (fun t ht ↦ step t (by omega))
    linarith [step T (by omega)]

/-- A ball of coordinatewise radius strictly below one half covers at most one
binary diagonal. Its center may have arbitrary real entries. -/
theorem uniqueDiagonal {n : ℕ} {x y : Fin n → Bool} (c : Fin n → ℝ)
    (hx : ∀ i, |(if x i then 1 else 0 : ℝ) - c i| < 1 / 2)
    (hy : ∀ i, |(if y i then 1 else 0 : ℝ) - c i| < 1 / 2) : x = y := by
  funext i
  have h := abs_lt.mp (hx i)
  have k := abs_lt.mp (hy i)
  cases e : x i <;> cases f : y i <;> simp_all <;> linarith

#print axioms driftBudget
#print axioms uniqueDiagonal

end SigabaNeo.Wall1
