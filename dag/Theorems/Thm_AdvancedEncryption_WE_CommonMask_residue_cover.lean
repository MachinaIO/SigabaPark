import Mathlib

theorem AdvancedEncryption.WE.CommonMask.residue_cover {I : Type} [Fintype I] (v : I → ZMod 3) (hn : ∑ i, v i ≠ 0) :
    (∑ i, v i * (∑ j, v j)) = 1 ∧ ∀ i, v i = 0 → v i * (∑ j, v j) = 0 := by
  sorry
