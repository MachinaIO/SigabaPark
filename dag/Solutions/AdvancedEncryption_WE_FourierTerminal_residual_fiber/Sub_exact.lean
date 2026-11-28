import Mathlib

theorem solution {V W K : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup K]
    (rows : V →+ W) (last : V →+ K) (u : K → V)
    (fixRows : ∀ x, rows (u x) = 0) (moveLast : ∀ x, last (u x) = x)
    (x : K) : ∃ e : V ≃ V, ∀ r, (rows (e r), last (e r)) = (rows r, last r + x) := by
  refine ⟨{ toFun := fun r => r + u x
            invFun := fun r => r - u x
            left_inv := fun r => by simp
            right_inv := fun r => by simp }, ?_⟩
  intro r
  change (rows (r + u x), last (r + u x)) = _
  simp [fixRows, moveLast]
