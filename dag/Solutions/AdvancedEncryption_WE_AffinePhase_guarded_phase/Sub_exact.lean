import Mathlib

theorem solution (z e h : ℤ) (hh : 2 < h) (he : -1 ≤ e ∧ e ≤ 1)
    (guard : 0 < (z + e) % h ∧ (z + e) % h < h-1) :
    z / h = (z + e) / h := by
  have hz := Int.emod_add_mul_ediv (z+e) h
  have lo : 0 ≤ (z+e)%h - e := by omega
  have hi : (z+e)%h - e < h := by omega
  have decomp : z = ((z+e)%h-e) + h*((z+e)/h) := by linarith
  calc
    z / h = (((z+e)%h-e) + h*((z+e)/h)) / h := congrArg (fun n : ℤ => n / h) decomp
    _ = (z+e)/h := by rw [Int.add_mul_ediv_left _ _ (by omega : h ≠ 0), Int.ediv_eq_zero_of_lt lo hi, zero_add]
