import Mathlib

theorem solution (delta ca cr qa qr q pairs p : ℝ)
    (acc : delta = 2*ca + qa) (rej : -delta = 2*cr + qr)
    (qa0 : 0 ≤ qa) (qr0 : 0 ≤ qr) (count : 2*pairs = q*(q-1))
    (ba : |ca| ≤ q*(2*p) + pairs*(4*p))
    (br : |cr| ≤ q*(2*p) + pairs*(4*p)) : |delta| ≤ 4*q^2*p := by
  have h : q*(2*p) + pairs*(4*p) = 2*q^2*p := by
    calc
      _ = 2*q*p + (2*pairs)*(2*p) := by ring
      _ = _ := by rw [count]; ring
  rw [h] at ba br
  by_cases hd : 0 ≤ delta
  · rw [abs_of_nonneg hd]
    have := (abs_le.mp br).1
    linarith
  · rw [abs_of_neg (lt_of_not_ge hd)]
    have := (abs_le.mp ba).1
    linarith
