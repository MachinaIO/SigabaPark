import Mathlib

theorem solution {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (T : E →ₗ[K] E) (V : Submodule K E) (W : ℕ → Submodule K E) (h0 : W 0 = V)
    (hs : ∀ n, W (n+1) = W n ⊓ (W n).comap T) :
    (∀ U : Submodule K E, U ≤ V → (∀ x ∈ U, T x ∈ U) → ∀ n, U ≤ W n) ∧
    (∀ n, W (n+1) ≠ W n → Module.finrank K (W (n+1)) < Module.finrank K (W n)) ∧
    (∀ n, W (n+1) = W n → ∀ x ∈ W n, T x ∈ W n) := by
  constructor
  · intro U hU hT n
    induction n with
    | zero => simpa [h0] using hU
    | succ n ih =>
      rw [hs]
      intro x hx
      exact ⟨ih hx, ih (hT x hx)⟩
  constructor
  · intro n ne
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne (by rw [hs]; exact inf_le_left) ne
  · intro n eq x hx
    have hx' : x ∈ W (n+1) := eq.symm ▸ hx
    rw [hs] at hx'
    exact hx'.2
