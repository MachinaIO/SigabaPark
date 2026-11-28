import Definitions.Def_SparseRainbowProjection

theorem solution {K U V : Type*} [Field K] [Fintype K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] (M : U →ₗ[K] V)
    [Fintype (LinearMap.ker M).dualAnnihilator] (r : ℕ) :
    Fintype.card (Fin r → (LinearMap.ker M).dualAnnihilator) *
      Fintype.card K ^ (Module.finrank K (LinearMap.ker M) * r) =
      Fintype.card K ^ (Module.finrank K U * r) := by
  rw [Fintype.card_fun, Fintype.card_fin, SparseRainbowProjection.badForms,
    ← pow_mul, ← pow_add, ← Nat.add_mul]
  rw [Nat.sub_add_cancel (Submodule.finrank_le (LinearMap.ker M))]
