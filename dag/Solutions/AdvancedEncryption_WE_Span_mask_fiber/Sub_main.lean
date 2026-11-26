import Mathlib

theorem solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [DecidableEq K] [DecidableEq W]
    (secret : V →ₗ[K] K) (view : V →ₗ[K] W) (dir : V)
    (hs : secret dir = 1) (hv : view dir = 0) (b c : K) (w : W) :
    Fintype.card {x : V // secret x = b ∧ view x = w} =
      Fintype.card {x : V // secret x = c ∧ view x = w} := by
  classical
  let d := (c-b) • dir
  have hd : secret d = c-b := by simp [d, hs]
  have hz : view d = 0 := by simp [d, hv]
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨x.val+d, by
      constructor
      · rw [map_add, x.property.1, hd]; abel
      · rw [map_add, x.property.2, hz, add_zero]⟩
    invFun := fun x => ⟨x.val-d, by
      constructor
      · rw [map_sub, x.property.1, hd]; abel
      · rw [map_sub, x.property.2, hz, sub_zero]⟩
    left_inv := fun x => Subtype.ext (add_sub_cancel_right ..)
    right_inv := fun x => Subtype.ext (sub_add_cancel ..) }
