import Mathlib

theorem AdvancedEncryption.WE.PermTrace.LocalNandSix {G : Type*} [Group G] (t s a b : G) (hinv : s * s = 1)
    (hrev : s * t * s = t⁻¹) (hab : a * b * a⁻¹ * b⁻¹ = t) (x y z : Bool) :
    (if z then t * s else 1) * (if x then a else 1) *
      (if y then b else 1) * (if x then a⁻¹ else 1) *
      (if y then b⁻¹ else 1) * (if z then s else 1) =
      if z == !(x && y) then t else 1 := by sorry
