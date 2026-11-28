import Mathlib

theorem solution (z e0 e1 : ℤ) (he0 : -1 ≤ e0 ∧ e0 ≤ 1) (he1 : -1 ≤ e1 ∧ e1 ≤ 1) :
    let lo := ((((4*z+e0)%16)+2)/4)%4
    let hi := ((((z+e1)%16)-lo+2)/4)%4
    lo + 4*hi = z%16 := by
  dsimp
  omega
