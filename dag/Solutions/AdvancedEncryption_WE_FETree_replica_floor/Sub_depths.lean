import Mathlib.Tactic.IntervalCases

theorem solution (d : ℕ) (hd : 1 ≤ d) (ht : d ≤ 7) :
    4529848320 ≤ 2 ^ d * 2 ^ (2 ^ (7 - d)) *
      ((List.range d).map (fun j => 2 ^ (7 - d) * 2 ^ j + 8)).prod := by
  interval_cases d <;> decide
