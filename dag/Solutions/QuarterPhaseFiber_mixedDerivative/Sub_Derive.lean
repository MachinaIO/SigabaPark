import Mathlib.Tactic

theorem solution {X V : Type*} [AddCommGroup V] (f : X → V) (a b : X → X)
    (U W : AddSubgroup V) (hu : ∀ x, f (a x) - f x ∈ U)
    (hw : ∀ x, f (b x) - f x ∈ W)
    (hi : ∀ y, y ∈ U → y ∈ W → y = 0) (x : X) (hc : a (b x) = b (a x)) :
    (f (a (b x)) - f (b x)) - (f (a x) - f x) = 0 := by
  apply hi
  · exact U.sub_mem (hu (b x)) (hu x)
  · have he : (f (a (b x)) - f (b x)) - (f (a x) - f x) =
        (f (b (a x)) - f (a x)) - (f (b x) - f x) := by rw [hc]; abel
    rw [he]
    exact W.sub_mem (hw (a x)) (hw x)
