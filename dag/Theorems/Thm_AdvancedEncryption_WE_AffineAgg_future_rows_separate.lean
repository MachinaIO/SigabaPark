import Mathlib

theorem AdvancedEncryption.WE.AffineAgg.future_rows_separate {I K : Type} [Fintype I] [Field K] (d d' : I → K) (e e' : K) :
    (∀ a : I → K, e + ∑ i, a i * d i = e' + ∑ i, a i * d' i) ↔
      e = e' ∧ d = d' := by
  sorry
