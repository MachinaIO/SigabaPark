import Mathlib.Data.Finset.Card

theorem AdvancedEncryption.WE.SignNoise.ambiguous_prefix_count (bins width : ℕ) (cuts : Finset ℕ) :
    ((Finset.range bins).filter (fun i ↦
      ∃ t ∈ cuts, i * width < t ∧ t < (i+1)*width)).card ≤ cuts.card := by
  sorry
