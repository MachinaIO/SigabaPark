import Mathlib

theorem solution {I F : Type} [Field F] (g : F → F) (hg : Function.Injective g)
    (a c : I → F) (ha : ∀ i, a i ≠ 0) :
    Function.Injective (fun t : I → F => fun i => c i + a i * g (t i)) := by
  intro t u h
  funext i
  exact hg (mul_left_cancel₀ (ha i) (add_left_cancel (congrFun h i)))
