import Definitions.Def_SparseRainbowProjection

theorem SparseRainbowProjection.fullBadBankCount {K U V : Type*} [Field K] [Fintype K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] (M : U →ₗ[K] V)
    [Fintype (LinearMap.ker M).dualAnnihilator] (r : ℕ) :
    Fintype.card (Fin r → (LinearMap.ker M).dualAnnihilator) *
      Fintype.card K ^ (Module.finrank K (LinearMap.ker M) * r) =
      Fintype.card K ^ (Module.finrank K U * r) := by sorry
