import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) : ⌊a - b⌋ ≤ ⌊a⌋ - ⌊b⌋ ∧ ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b⌋ + 1 := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  have hc := Int.floor_le (a - b)
  have hc' := Int.lt_floor_add_one (a - b)
  constructor
  · have : ((⌊a - b⌋ : ℤ) : ℝ) < ((⌊a⌋ - ⌊b⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  · have : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < ((⌊a - b⌋ + 1 + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
