import Mathlib

theorem AdvancedEncryption.WE.PublicSlices.joint_slice_shifts {K E F I J S : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (u : I → F →ₗ[K] K) (v : J → E) (B : S → E →ₗ[K] F) :
    (∀ s i j, u i (B s (v j)) = 0) ↔
    ∃ D : S → E →ₗ[K] F, (∀ s i x, u i (D s x) = 0) ∧
      (∀ s j, D s (v j) = B s (v j)) := by
  sorry
