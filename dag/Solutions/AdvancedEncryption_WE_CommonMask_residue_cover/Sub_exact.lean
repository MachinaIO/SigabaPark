import Mathlib

theorem solution {I : Type} [Fintype I] (v : I → ZMod 3) (hn : ∑ i, v i ≠ 0) :
    (∑ i, v i * (∑ j, v j)) = 1 ∧ ∀ i, v i = 0 → v i * (∑ j, v j) = 0 := by
  constructor
  · rw [← Finset.sum_mul]
    exact (by decide : ∀ a : ZMod 3, a ≠ 0 → a*a = 1) _ hn
  · intro i hv
    simp [hv]
