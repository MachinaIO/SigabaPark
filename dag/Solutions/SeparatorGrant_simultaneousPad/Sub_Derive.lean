import Mathlib.Tactic

theorem solution {I G : Type*} [AddGroup G] (offset : I → G) :
    Function.Bijective (fun pad : I → G => fun i => offset i + pad i) := by
  constructor
  · intro x y h
    funext i
    exact add_left_cancel (congrFun h i)
  · intro y
    refine ⟨fun i => -offset i + y i, ?_⟩
    funext i
    simp
