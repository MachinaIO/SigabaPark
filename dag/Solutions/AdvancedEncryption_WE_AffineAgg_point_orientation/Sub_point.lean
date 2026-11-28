import Mathlib

theorem solution (o p₀ p₁ p₂ r₀ r₁ r₂ s : Bool) :
    Bool.xor (Bool.xor (Bool.xor (Bool.xor o (p₀ && (Bool.xor true r₀))) (p₁ && r₁)) (p₂ && r₂)) s
      = Bool.xor o (Bool.xor (Bool.xor (Bool.xor (p₀ && (Bool.xor true r₀)) (p₁ && r₁)) (p₂ && r₂)) s) := by
  cases o <;> cases p₀ <;> cases p₁ <;> cases p₂ <;> cases r₀ <;> cases r₁ <;> cases r₂ <;> cases s <;> rfl
