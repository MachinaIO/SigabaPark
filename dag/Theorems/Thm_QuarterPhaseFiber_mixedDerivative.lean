import Mathlib.Tactic

theorem QuarterPhaseFiber.mixedDerivative {X V : Type*} [AddCommGroup V] (f : X → V) (a b : X → X)
    (U W : AddSubgroup V) (hu : ∀ x, f (a x) - f x ∈ U)
    (hw : ∀ x, f (b x) - f x ∈ W)
    (hi : ∀ y, y ∈ U → y ∈ W → y = 0) (x : X) (hc : a (b x) = b (a x)) :
    (f (a (b x)) - f (b x)) - (f (a x) - f x) = 0 := by
  sorry
