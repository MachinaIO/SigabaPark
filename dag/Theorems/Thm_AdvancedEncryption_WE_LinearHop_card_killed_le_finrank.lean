import Mathlib

/-- Per-hop kill count (note `pq-we-linear-hop-barrier`): at most `finrank K V` indices `r` have a
hop embedding `L r` that is invisible to every later functional `h t` (`t > r`) but visible to
`h r`. -/
theorem AdvancedEncryption.WE.LinearHop.card_killed_le_finrank {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {M : ℕ}
    (h : Fin M → Module.Dual K V) (L : Fin M → (U →ₗ[K] V)) :
    {r | (∀ t, r < t → (h t).comp (L r) = 0) ∧ (h r).comp (L r) ≠ 0}.ncard
      ≤ Module.finrank K V := by sorry
