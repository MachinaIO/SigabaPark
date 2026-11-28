import Mathlib

theorem solution {K U V H : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype U] (L : U →ₗ[K] V)
    (cert : U) (target : V) (valid : L cert = target) (phase : H → K)
    (test : H → V → ℤ) (h : H) :
    (∑ u : U, test h (L u + phase h • target)) = ∑ u : U, test h (L u) := by
  classical
  calc
    _ = ∑ u : U, test h (L (u + phase h • cert)) := by simp [valid]
    _ = ∑ u : U, test h (L u) :=
      Equiv.sum_comp (Equiv.addRight (phase h • cert)) (fun x => test h (L x))
