import Mathlib.Logic.Function.Basic

theorem AdvancedEncryption.WE.FusedRank.row_reindex {X Y K A : Type} (row : X → K) (col : X → Y → A)
    (rows : Function.Surjective row) (cols : ∀ x, Function.Surjective (col x)) :
    Function.Surjective (fun p : X × Y => (row p.1, col p.1 p.2)) := by
  sorry
