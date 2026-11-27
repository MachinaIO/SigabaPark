import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.backsolve_length {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (choose : V → (V →ₗ[K] K)) (cs : List V) (H : V →ₗ[K] V) (v : V) :
    (backsolve choose cs H v).length = cs.length := by sorry
