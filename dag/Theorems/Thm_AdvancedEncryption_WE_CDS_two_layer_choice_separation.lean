import Mathlib

theorem AdvancedEncryption.WE.CDS.two_layer_choice_separation {W H I J : Type*} [Fintype W] [Fintype H]
    (row : W → H) (root : W → I → Bool) (db : W → J → Bool)
    (hdb : Function.Injective db) (hcount : Fintype.card H < Fintype.card W) :
    ∃ u v, u ≠ v ∧ row u = row v ∧
      ((∃ i, root u i ≠ root v i) ∨ (root u = root v ∧ ∃ j, db u j ≠ db v j)) := by sorry
