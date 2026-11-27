import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.image_reach {K V U : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] (P : V →ₗ[K] U) (cs : List V) (z : U) :
    Reach K (cs.map P) z ↔ ∃ v, Reach K cs v ∧ P v = z := by sorry
