import Mathlib

theorem AdvancedEncryption.WE.BinaryBilinear.support_codimension {I Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Fintype Q]
    (s : Finset I) (odd : Odd s.card) (v : I → Q) (hn : ∀ i ∈ s, v i ≠ 0)
    (hz : ∑ i ∈ s, v i = 0) : 2 ≤ Module.finrank (ZMod 2) Q := by
  sorry
