import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.DirectedLabels.decoding_error {I : Type} [Fintype I] (c e : I → ℤ) (delta W B : ℤ)
    (hd : |delta| ≤ B) (hw : ∀ i, |e i| ≤ W) :
    |delta - ∑ i, c i * e i| ≤ B + (∑ i, |c i|) * W := by sorry
