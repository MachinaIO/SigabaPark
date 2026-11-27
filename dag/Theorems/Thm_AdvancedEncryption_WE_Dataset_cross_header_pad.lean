import Mathlib

theorem AdvancedEncryption.WE.Dataset.cross_header_pad {Y : Type*} [AddCommGroup Y] (sV sG e₀ e₁ c₀ c₁ : Y)
    (h₀ : c₀ = sV + e₀) (h₁ : c₁ = sV - sG + e₁) :
    c₀ - c₁ = sG + (e₀ - e₁) := by
  sorry
