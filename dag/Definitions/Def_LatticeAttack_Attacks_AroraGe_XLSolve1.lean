module

public import Mathlib.Algebra.Polynomial.Roots
set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

open Polynomial

/-- A nonconstant affine change of variable preserves the number of distinct roots. -/
theorem affine_root_set_card {K : Type*} [Field K] [DecidableEq K]
    (E : Finset K) (a b : K) (ha : a ≠ 0) :
    (E.image (fun r ↦ (b - r) / a)).card = E.card := by
  apply Finset.card_image_of_injective
  intro r t h
  exact sub_right_inj.mp ((div_left_inj' ha).mp h)

/-- The roots of the product are the inverse images of the specified field elements. -/
theorem affine_product_eval_zero_iff {K : Type*} [Field K] [DecidableEq K]
    (E : Finset K) (a b x : K) :
    (∏ r ∈ E, (C b - C a * X - C r)).eval x = 0 ↔ b - a * x ∈ E := by
  simp [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

#print axioms affine_root_set_card
#print axioms affine_product_eval_zero_iff

end SigabaNeo.Lattices.AroraGe
