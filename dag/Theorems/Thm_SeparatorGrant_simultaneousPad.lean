import Mathlib.Tactic

theorem SeparatorGrant.simultaneousPad {I G : Type*} [AddGroup G] (offset : I → G) :
    Function.Bijective (fun pad : I → G => fun i => offset i + pad i) := by
  sorry
