import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution (x y : Bool) (k : ℤ) :
    ((x.toNat : ℤ) - y.toNat)^2 ≤ ((x.toNat : ℤ) - y.toNat + 2*k)^2 := by
  cases x <;> cases y <;> simp <;>
    first | positivity | (by_contra! h; rw [abs_lt] at h; omega)
