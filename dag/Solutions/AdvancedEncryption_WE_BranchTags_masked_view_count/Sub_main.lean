import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel

theorem solution
    {X R G : Type*} [Finite X] [AddCommGroup R] [Finite R] [AddCommGroup G]
    (f : X → G) (mask : R →+ G) (y : G) :
    Nat.card {p : X × R // f p.1 + mask p.2 = y} =
      Nat.card {x : X // ∃ r, f x + mask r = y} * Nat.card mask.ker := by
  classical
  let C := {x : X // ∃ r, f x + mask r = y}
  let pick (x : C) : R := x.property.choose
  have hp (x : C) : f x.val + mask (pick x) = y := x.property.choose_spec
  let project (p : {p : X × R // f p.1 + mask p.2 = y}) : C :=
    ⟨p.val.1, p.val.2, p.property⟩
  let e : {p : X × R // f p.1 + mask p.2 = y} ≃ C × mask.ker := {
    toFun := fun p ↦ (project p, ⟨p.val.2 - pick (project p), by
      change mask (p.val.2 - pick (project p)) = 0
      rw [map_sub, sub_eq_zero]
      exact add_left_cancel (p.property.trans (hp (project p)).symm)⟩)
    invFun := fun z ↦ ⟨(z.1.val, z.2.val + pick z.1), by
      change f z.1.val + mask (z.2.val + pick z.1) = y
      rw [map_add, show mask z.2.val = 0 from z.2.property, zero_add]
      exact hp z.1⟩
    left_inv := fun p ↦ by
      apply Subtype.ext
      exact Prod.ext rfl (sub_add_cancel _ _)
    right_inv := fun z ↦ by
      apply Prod.ext
      · exact Subtype.ext rfl
      · apply Subtype.ext
        change z.2.val + pick z.1 - pick z.1 = z.2.val
        abel }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)
