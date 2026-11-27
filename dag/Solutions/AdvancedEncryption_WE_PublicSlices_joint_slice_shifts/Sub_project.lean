import Mathlib

theorem solution {K E F I J S : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (u : I → F →ₗ[K] K) (v : J → E) (B : S → E →ₗ[K] F) :
    (∀ s i j, u i (B s (v j)) = 0) ↔
    ∃ D : S → E →ₗ[K] F, (∀ s i x, u i (D s x) = 0) ∧
      (∀ s j, D s (v j) = B s (v j)) := by
  constructor
  · intro h
    let W := Submodule.span K (Set.range v)
    obtain ⟨Q,hQ⟩ := W.exists_isCompl
    let p := W.projection Q hQ
    refine ⟨fun s => (B s).comp p, ?_, ?_⟩
    · intro s i x
      have hw : W ≤ LinearMap.ker ((u i).comp (B s)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        exact h s i j
      exact hw (W.projection_apply_mem hQ x)
    · intro s j
      have hv : v j ∈ W := Submodule.subset_span (Set.mem_range_self j)
      change B s (W.projection Q hQ (v j)) = B s (v j)
      rw [W.projection_apply_of_mem_left hQ hv]
  · rintro ⟨D,h₁,h₂⟩ s i j
    rw [← h₂ s j]
    exact h₁ s i (v j)
