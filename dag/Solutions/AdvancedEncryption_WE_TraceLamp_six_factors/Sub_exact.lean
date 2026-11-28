import Mathlib

theorem solution (x y z : Bool) :
    let b := fun v : Bool ↦ if v then (1 : ℤ) else 0
    let X := b x
    let Y := b y
    let T := b (!z)
    let mul := fun (a d : ℤ × ℤ × ℤ) ↦
      (a.1 + d.1, a.2.1 + d.2.1, a.2.2 + d.2.2 + a.1 * d.2.1)
    let q := mul (mul (mul (mul (mul (X,0,0) (0,Y,0)) (2*T,-2*T,0))
      (-X,0,0)) (0,-Y,0)) (-2*T,2*T,-4*T*T+3*T)
    q = (0,0,X*Y-2*X*T-2*Y*T+3*T) ∧
      ((q.2.2 = 0 ↔ z = !(x && y)) ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ 3) := by
  cases x <;> cases y <;> cases z <;> decide
