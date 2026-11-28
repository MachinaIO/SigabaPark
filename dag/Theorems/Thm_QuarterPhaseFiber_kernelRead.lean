import Mathlib.Tactic

theorem QuarterPhaseFiber.kernelRead {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ZMod 2) (d z : I → ZMod 2) (s : J → ZMod 2)
    (hd : ∀ j, (∑ i, d i * A j i) = 0) :
    (∑ i, d i * ((∑ j, A j i * s j) + z i)) = ∑ i, d i * z i := by
  sorry
