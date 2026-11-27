import Mathlib

theorem solution (w : ℕ) (hw : 1 ≤ w) :
    4923756544 ≤ 4096 * (3^(w-1) + 24320 * ((512+w-1)/w)) := by
  by_cases h : w ≤ 13
  · interval_cases w <;> norm_num
  · have hpow : (3:ℕ)^13 ≤ 3^(w-1) := by gcongr; omega
    norm_num at hpow
    omega
