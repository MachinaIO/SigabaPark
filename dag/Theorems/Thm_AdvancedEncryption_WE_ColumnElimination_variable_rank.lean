import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.variable_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (choose : V → (V →ₗ[K] K)) (spec : ∀ a, a = 0 ∨ choose a a = 1)
    (cs : List V) (H : V →ₗ[K] V) (v : V) :
    Reach K (cs.map H) (H v) ↔ terminal choose cs H v = 0 := by sorry
