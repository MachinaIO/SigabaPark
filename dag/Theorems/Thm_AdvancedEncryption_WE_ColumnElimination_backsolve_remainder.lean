import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.backsolve_remainder {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (choose : V → (V →ₗ[K] K)) (cs : List V) (H : V →ₗ[K] V) (v : V) :
    H v - H (weighted cs (backsolve choose cs H v)) = terminal choose cs H v := by sorry
