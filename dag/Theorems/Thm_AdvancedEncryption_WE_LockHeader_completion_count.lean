import Mathlib

theorem AdvancedEncryption.WE.LockHeader.completion_count {α : Type*} [Fintype α] [DecidableEq α]
    (queried good₀ good₁ : Finset α)
    (miss : ∀ k, k ∉ queried → k ∈ good₀ → k ∉ good₁) :
    good₀.card + good₁.card ≤ Fintype.card α + queried.card := by sorry
