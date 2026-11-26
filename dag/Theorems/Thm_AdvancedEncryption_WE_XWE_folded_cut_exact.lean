import Mathlib.Data.Finset.Union

theorem AdvancedEncryption.WE.XWE.folded_cut_exact {S : Type} [DecidableEq S] (layers : List (Finset (S → S)))
    (initial : Finset S) (z : S) :
    z ∈ layers.foldl (fun states layer ↦ states.biUnion fun s ↦ layer.image (fun f ↦ f s)) initial ↔
    ∃ s ∈ initial, ∃ path : List (S → S),
      List.Forall₂ (fun f layer ↦ f ∈ layer) path layers ∧
      path.foldl (fun t f ↦ f t) s = z := by
  sorry
