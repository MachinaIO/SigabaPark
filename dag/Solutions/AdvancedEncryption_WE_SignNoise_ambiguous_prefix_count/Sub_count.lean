import Mathlib.Data.Finset.Card

theorem solution (bins width : ℕ) (cuts : Finset ℕ) :
    ((Finset.range bins).filter (fun i ↦
      ∃ t ∈ cuts, i * width < t ∧ t < (i+1)*width)).card ≤ cuts.card := by
  apply le_trans (Finset.card_le_card (t := cuts.image (fun t ↦ t / width)) ?_)
    (Finset.card_image_le)
  intro i hi
  obtain ⟨_,t,ht,hlo,hhi⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_image.mpr ⟨t,ht,?_⟩
  exact Nat.div_eq_of_lt_le hlo.le hhi
