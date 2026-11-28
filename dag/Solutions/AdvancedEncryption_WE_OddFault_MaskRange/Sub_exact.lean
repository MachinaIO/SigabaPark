import Mathlib

theorem solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (g : W) :
    (∀ z : K, ∃ u : V, ∀ v : V, M (v + u) = z • g + M v) ↔ g ∈ M.range := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h 1
    exact ⟨u, by simpa using hu 0⟩
  · rintro ⟨u, rfl⟩ z
    exact ⟨z • u, fun v ↦ by simp [add_comm]⟩
