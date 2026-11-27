import Mathlib

theorem AdvancedEncryption.WE.AffineAgg.point_orientation (o p₀ p₁ p₂ r₀ r₁ r₂ s : Bool) :
    Bool.xor (Bool.xor (Bool.xor (Bool.xor o (p₀ && (Bool.xor true r₀))) (p₁ && r₁)) (p₂ && r₂)) s
      = Bool.xor o (Bool.xor (Bool.xor (Bool.xor (p₀ && (Bool.xor true r₀)) (p₁ && r₁)) (p₂ && r₂)) s) := by
  sorry
