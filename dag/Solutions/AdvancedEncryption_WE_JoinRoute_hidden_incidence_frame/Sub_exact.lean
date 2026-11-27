import Mathlib

theorem solution {E V G : Type} [AddCommGroup G] (dest : E → V) (key : V → G) (other : E → G) :
    Function.Bijective (fun (pad : E → G) (e : E) ↦ key (dest e) + other e + pad e) := by
  constructor
  · intro a b hab
    funext e
    exact add_left_cancel (congrFun hab e)
  · intro frame
    refine ⟨fun e ↦ frame e - (key (dest e) + other e),?_⟩
    funext e
    dsimp
    abel
