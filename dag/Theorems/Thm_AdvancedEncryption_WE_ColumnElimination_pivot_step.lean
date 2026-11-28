import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.pivot_step {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (a : V) (l : V →ₗ[K] K) (hl : a = 0 ∨ l a = 1) (cs : List V) (v : V) :
    Reach K (a :: cs) v ↔ Reach K (cs.map (kill a l)) (kill a l v) := by sorry
