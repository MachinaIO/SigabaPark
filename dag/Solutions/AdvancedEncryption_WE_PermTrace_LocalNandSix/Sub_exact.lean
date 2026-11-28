import Mathlib

theorem solution {G : Type*} [Group G] (t s a b : G) (hinv : s * s = 1)
    (hrev : s * t * s = t⁻¹) (hab : a * b * a⁻¹ * b⁻¹ = t) (x y z : Bool) :
    (if z then t * s else 1) * (if x then a else 1) *
      (if y then b else 1) * (if x then a⁻¹ else 1) *
      (if y then b⁻¹ else 1) * (if z then s else 1) =
      if z == !(x && y) then t else 1 := by
  have step : t * s * a * b * a⁻¹ * b⁻¹ * s = 1 := by
    calc
      _ = t * (s * (a * b * a⁻¹ * b⁻¹) * s) := by group
      _ = 1 := by rw [hab, hrev, mul_inv_cancel]
  cases x <;> cases y <;> cases z <;> simp_all [mul_assoc]
