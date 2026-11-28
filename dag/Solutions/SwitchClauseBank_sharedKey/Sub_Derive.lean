import Mathlib.Tactic

theorem solution {I X : Type*} [Fintype I] (g : I → X → ZMod 2)
    (w : I → ZMod 2) (hw : ∀ x, (∑ i, w i * g i x) = 1)
    (r : I → ZMod 2) (x : X) :
    (∑ i, (r i + w i) * g i x) = (∑ i, r i * g i x) + 1 := by
  simp only [add_mul, Finset.sum_add_distrib, hw]
