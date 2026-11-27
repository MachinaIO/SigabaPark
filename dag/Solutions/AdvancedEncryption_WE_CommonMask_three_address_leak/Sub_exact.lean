import Mathlib

theorem solution (b a₀ a₁ d₀ d₁ c₀₁ c₁₀ c₁₁ : Bool) :
    let e₀₁ := b ^^ a₀ ^^ d₁ ^^ c₀₁
    let e₁₀ := b ^^ a₁ ^^ d₀ ^^ c₁₀
    let e₁₁ := b ^^ a₁ ^^ d₁ ^^ c₁₁
    e₀₁ ^^ e₁₀ ^^ e₁₁ ^^ a₀ ^^ d₀ ^^ c₀₁ ^^ c₁₀ ^^ c₁₁ = b := by
  revert b a₀ a₁ d₀ d₁ c₀₁ c₁₀ c₁₁
  decide
